# STATUS: TRY_OPENSGN_EXACT_LAPLACE_EVALUATION_WITH_POISSON_REMAINDER
```yaml
PRIMARY: TRY_OPENSGN_EXACT_LAPLACE_EVALUATION_WITH_POISSON_REMAINDER
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_OPENSGN_EXACT_LAPLACE_EVALUATION_WITH_POISSON_REMAINDER
RESULT: PARTIAL_WITH_PRECISE_REMAINDER
PARTIAL_SCOPE: exact_evaluation_and_remainder_reduction_not_arithmetic_coefficient_closure
REQUEST_ID: REQ-2026-09-06-OPENSGN
BOUNDARY_ID: GOAL058_OPEN_SIGNED_TIME_KERNEL_IDENTITY
REQUEST_LOCK:
  COMMIT: 90aaa56a0dbfdd1e86887329dc97f75ae2aa12fc
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_OPEN_SIGNED_TIME_KERNEL_IDENTITY_2026-09-06.txt
  GIT_BLOB: 0d4143ec66be997ad0dbdf550f3d65e4e59c28bf
  SHA256: d01fd4bf054a73c9ace3d9db63a8a33cbd78189fd51227d8fced57a64754bc5f
  BYTES: 6882
  LINES: 71
  FINAL_LF: true
  FETCHED_UTF8_REENCODING_HASHES_INDEPENDENTLY_RECOMPUTED: true
PARENT_LOCK:
  GIT_BLOB: ec3d34b7fc711077ea5473aa705390b1c676bcea
  SHA256: 146939ed954e20e9e0a26b21eca1d36bb74721d7238b38772b60f690bb1a71b2
  MOUNTED_BYTES_MATCH_PINNED_GITHUB_BLOB: true
EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_OPEN_SIGNED_TIME_KERNEL_IDENTITY_2026-09-06.md
PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_SECOND_EXPRESSION
  SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
  TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false
CLOSES: [REQ-2026-09-06-OPENSGN]
CLOSES_ANALYTIC_RH_SUPPLIERS: []
OPENS: []
MAIN_OPEN_IDENTITY_PROVED: false
NEW_TARGET_COEFFICIENTS_REPRODUCED_FROM_V:
  ARCHIMEDEAN_FINITE_PART: false
  ARCHIMEDEAN_DELTA_CONSTANT: false
  COMPLETE_PRIME_ATOMS_WITH_COEFFICIENT_ONE: false
PROVED_HERE:
  - signed_Volterra_derivative_without_the_nonexistent_gprime_at_zero
  - distributional_three_term_evaluation_and_explicit_prime_shift_operators
  - exact_double_Laplace_formulas_in_both_sign_quadrants
  - exact_vanishing_of_the_eta_part_on_equal_positive_Laplace_parameters
  - full_signed_identity_equivalent_to_one_explicit_Poisson_integral_identity
  - exact_scalar_transform_description_of_the_full_distributional_remainder
  - planted_failures_at_the_Poisson_reconstruction_step
  - quantitative_consistency_with_the_signed_radical_cutoff_check
SCOPED_REJECTIONS:
  - finite_gprime_zero_boundary_term
  - negative_prime_sign_in_gsecond_rather_than_in_minus_gsecond
  - eta_part_alone_equals_the_target_prime_distribution
  - known_boundary_unitarity_automatically_implies_Poisson_reconstruction
CURRENT_UNEVALUATED_INTEGRAL: >-
  (1/pi) integral_R p*X(x)^2/((p^2+x^2)*(X(x)^2+Xprime(x)^2)) dx
  = xi(1/2+p)/(xi(1/2+p)+xi_prime(1/2+p)), for every p>1/2.
THIS_IS_NOT_A_WEAKER_RH_PREMISE: true
SIGNED_OBJECT_CHANGED: false
PRINTED_EVEN_OBJECT_REINTRODUCED: false
EXTERNAL_RH_BASIS_USED: false
DIRECT_EVALUATION_USES_ZERO_SUMS: false
AUXILIARY_RADICAL_AND_PLANTS_USE_UNCONDITIONAL_ZERO_FORMULAS: true
SCOPE: ABSTRACT
VERIFIER: PAPER
INDEPENDENT_LEAN_VERIFICATION: false
NOVELTY_IN_THE_LITERATURE: not_claimed
LEAN_EDIT_PERFORMED: false
NUMERICAL_RUN_PERFORMED: false
ARISTOTLE_SUBMISSION: false
REPOSITORY_WRITE_SCOPE: EXPECTED_VERDICT_DOCUMENT_ONLY
ROUTE_PROMOTION: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
NEGATION_OF_RH_CLAIM: false
```

## 0. Verdict and evidence boundary

The signed object is retained exactly. The full identity (OPEN) is not proved. The calculation below evaluates its two time integrations, rather than assuming an RH-dependent spectral resolution. It leaves one explicitly specified real-axis Poisson integral unevaluated. Its defect, together with an explicit phase-dispersion defect, determines the full distributional remainder by formulas (L++) and (L+-).

A substantive falsifier emerges: the **entire eta contribution has zero double Laplace transform when both positive-time parameters are equal**. The target prime distribution does not. Thus the suggested allocation “omega supplies the archimedean part; eta transports the prime atoms” cannot be an exact allocation of those distributions. All arithmetic, including the primes, must already be present in the omega average on that diagonal.

No new finite-part or prime coefficient has been separately reproduced from V. This is a partial **evaluation** with a reduced, quantified remainder, not the stronger partial coefficient-closure illustrated in the request. In particular, writing down the target prime series is not credited as extracting it from the norm integral.

### Sources used

[R] The fetched request at the commit above. Its decoded UTF-8 content was re-encoded locally; SHA-256, Git object SHA-1, bytes, line count and final LF all match. No Unicode normalization was applied.

[P] The complete SECONDEXPR-B verdict, including append-only section 10, blob `ec3d34b7fc711077ea5473aa705390b1c676bcea`, read at the request commit and compared with the mounted 43,070-byte file. Sections 3, 5, 7 and 8 supply the definitions, not a hypothesis that the signed identity holds.

[Q] `paper_weil/sections/setup.tex` at the request commit, blob `8637e3d973ba689c0cfd5d09a10e2dec3edd3caa`. It fixes the full complex test class, Fourier conventions, Weil criterion and the control-space bound. The canonical test and cutoff data are those identified in [P], with Fourier transform X/A.

[S] M. Suzuki, *On the Hilbert space derived from the Weil distribution*, arXiv:2301.00421v3, equations (1.5)-(1.9), (4.3)-(4.10). PDF pages 3, 11 and 12 were inspected. Only the positive-time source formula is used; the previously disputed even-time extension is not imported.

[T] Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096v2, section 2.5, together with the independently checked finite-part convention in [P]. Global temperedness of g or T is not inferred from continuity; the arithmetic distributions act on compact smooth tests.

All new derivations below are PAPER, with no claim of priority or kernel verification. Historical diagnostics, other agent results, and the finite-stencil theorem are not mathematical premises of this computation.

## 1. Exact definitions, endpoint repair, and weak derivatives — 1(a), 1(f)

Write g=g_xi, X(z)=xi(1/2-iz)=Xi(z), and use

\[
\mathsf F_-f(x)=\int f(r)e^{-ixr}dr,
\qquad \langle F,G\rangle_2=\int F\overline G.
\]

Set

\[
\alpha(x)=\frac{X'(x)}{X(x)-iX'(x)},\qquad
\beta(x)=\frac{X(x)}{X(x)-iX'(x)},
\]

with removable values at real zeros. Then

\[
|\alpha|^2=1-\omega,\quad |\beta|^2=\omega,
\quad\alpha\overline\beta=\eta\in\mathbb R,
\quad0\le\omega\le1,\quad |\eta|\le\tfrac12.
\tag{1}
\]

The signed a_t,b_t,A_t,B_t in [R] give, for every real t,

\[
A_t(x)=\int_0^t e^{-ixr}dr,\quad
B_t(x)=\int_0^t e^{-ix(t-r)}g'(r)dr,
\qquad S_t=\alpha A_t-i\beta B_t.
\tag{2}
\]

Both integrals are oriented integrals; at t=0 they vanish. These equations are precisely the signed repair, not the printed even object.

### Lemma 1: the correct differentiated data [ABSTRACT][PAPER]

For every fixed real x, locally in t in the distributional and almost-everywhere senses,

\[
\partial_t A_t=e^{-ixt}=:e_t(x),\qquad
\partial_t B_t=g'(t)-ixB_t=:C_t(x).
\tag{3}
\]

There is **no finite boundary value g'(0+)** to substitute. In the stated finite-part scale,

\[
g'(t)=\tfrac12\log t+\tfrac12(\gamma_E+\log(2\pi))+O(t)
\quad(t\downarrow0).
\tag{4}
\]

**Proof.** The first identity is differentiation of an oriented integral, valid on both half-lines. The second follows by differentiating the integrating-factor formula in (2); g' is locally integrable, in fact locally square-integrable. The explicit source derivative is, for t>0 away from prime hinges,

\[
g'(t)=-4\sinh(t/2)+\sum_{n\le e^t}w_n+\frac{c_A}{2}
-\frac12 e^{-t/2}\Phi(e^{-2t},1,1/4),
\tag{5}
\]

where c_A=gamma_E+log(8pi)+pi/2. Its logarithmic endpoint expansion is (4), also obtained by integrating the pinned T=-g'' near zero. Formula (3) therefore includes the endpoint correctly without separating two divergent terms. B_t is continuous through zero and every prime hinge, so its first derivative contains no extra point mass in t. QED.

The sign in request 1(c) also needs a local correction: **g'' has +w_n atoms**, whereas T=-g'' has -w_n atoms. The task's displayed definition of T is retained; its prose sentence assigning minus atoms to g'' is not used.

### Lemma 2: each differentiated Gram term is a well-defined distribution [ABSTRACT][PAPER]

For epsilon>0 multiply the spectral integrands by exp(-epsilon*x^2). Then

\[
\begin{split}
\partial_t\partial_u V_\epsilon(t,u)=\frac1\pi\int e^{-\epsilon x^2}
\bigl[&\omega(C_t\overline{C_u}-e_t\overline{e_u})\\
&+i\eta(e_t\overline{C_u}-C_t\overline{e_u})\bigr]dx.
\end{split}
\tag{6}
\]

The limit of (6) as epsilon decreases to zero exists in D'(R^2) and equals partial_t partial_u V_sgn. Thus (6), with this limit, is an explicit answer to 1(a), not an unjustified ordinary integral of differentiated L2 functions.

**Proof.** On every finite time interval g' is L2; at fixed epsilon, the polynomial-in-x bounds from (3) are integrable with the Gaussian, so weak differentiation and Fubini are legitimate. The families a_t,b_t are continuous and bounded in L2 on compact time intervals. Consequently their Fourier transforms form compact subsets of L2. Strong convergence of the Gaussian multipliers to identity is uniform on these compact subsets. Cauchy-Schwarz gives locally uniform convergence V_epsilon -> V_sgn, hence distributional convergence of their derivatives. QED.

An equivalent formula avoiding spectral regularization on separable tests is useful. For f supported in [-T0,T0], define the actual compactly supported L2 function

\[
(\mathcal Bf)(r)=-\int b_t(r)f'(t)dt
=\begin{cases}
-\int_0^\infty g'(s)f'(r+s)ds,&r>0,\\
-\int_0^\infty g'(s)f'(r-s)ds,&r<0.
\end{cases}
\tag{7}
\]

Its value at zero is immaterial. Minkowski gives

\[
\|\mathcal Bf\|_2\le G_2(T_0)\|f'\|_1,
\qquad G_2(T_0)=\|g'\|_{L^2(0,T_0)}.
\tag{8}
\]

With F_f=F_-f and L_f=F_-(Bf), formula (6) paired with f(t)conj(h(u)) becomes the absolutely convergent integral

\[
\frac1\pi\int\bigl[
\omega(L_f\overline{L_h}-F_f\overline{F_h})
+i\eta(F_f\overline{L_h}-L_f\overline{F_h})\bigr]dx.
\tag{9}
\]

Indeed -integral A_t f'(t)dt=F_-f and -integral B_t f'(t)dt=F_-(Bf), first as Bochner integrals and then by Plancherel. A bound for (9) is

\[
2\|\mathcal Bf\|_2\|\mathcal Bh\|_2+2\|f\|_2\|h\|_2
+\|f\|_2\|\mathcal Bh\|_2+\|\mathcal Bf\|_2\|h\|_2.
\tag{10}
\]

No value at a spectral zero or at the temporal logarithmic endpoint has been suppressed.

## 2. Translation-invariant and prime pieces actually obtained — 1(b), 1(c)

The -omega*A_t*conj(A_u) term in V has differentiated kernel

\[
-W(t-u),\qquad
W(v)=\frac1\pi\mathcal F_{x\to v}^{(-)}\omega
      =\frac1\pi\int\omega(x)e^{-ixv}dx
\quad\text{in }\mathcal S'.
\tag{11}
\]

This is translation-invariant. The C_t*conj(C_u) and eta terms in (6) include anchored Volterra data and are not separately shown to depend only on t-u. Their required cancellation is not automatic.

In particular (11) by itself cannot equal a nonzero multiple of Pf(1/|v|) plus a locally integrable function and a locally finite measure. Every compact smooth localization of W has bounded Fourier transform, because it is a convolution of bounded omega with a Schwartz function. A localization of Pf(1/|v|) equal to it near zero has Fourier growth -2 log|x|+O(1); localized L1 functions and finite measures have bounded transforms. This proves that the missing archimedean singularity cannot simply be assigned to the -AA term. It may emerge only after the other terms are evaluated.

### Lemma 3: the exact prime operators in the differentiated Volterra data [ABSTRACT][PAPER]

Let ell_n=log n. The contribution of the nth prime power to B_t is

\[
B_t^{[n]}(x)=w_n\,\operatorname{sgn}(t)
\mathbf1_{|t|>\ell_n}\,A_{t-\operatorname{sgn}(t)\ell_n}(x),
\]

and its derivative is

\[
C_t^{[n]}(x)=w_n\,\operatorname{sgn}(t)
\mathbf1_{|t|>\ell_n}\,e^{-ix(t-\operatorname{sgn}(t)\ell_n)}.
\tag{12}
\]

Equivalently, in (7),

\[
\mathcal B=\mathcal B_0+\sum_{\ell_n<T_0}w_nJ_n,
\quad
(J_nf)(r)=\mathbf1_{r>0}f(r+\ell_n)
          -\mathbf1_{r<0}f(r-\ell_n),
\tag{13}
\]

where B_0 is obtained by deleting the prime-step sum in (5). This is a finite sum for the specified tests. Each J_n has L2 norm at most one.

**Proof.** Insert the step w_n*1_(s>ell_n) in g'(s) for positive s and its odd extension for negative s into (2). The resulting oriented integral is (12)'s antiderivative. At activation A_0=0, so differentiation introduces a step, not an additional delta. In (7), integrate f' over the indicated half-line; its endpoints give the two shifted evaluations in (13). The norm assertion follows from their disjoint supports and a change of variable. QED.

For clarity the extra multipliers can now be written before evaluation. Let L_f^0=F_-(B_0 f), Z_n f=F_-(J_n f). The prime-dependent part of (9) is exactly

\[
\begin{split}
\frac1\pi\int \biggl\{\omega\biggl[&\sum_n w_n
 (Z_nf\,\overline{L_h^0}+L_f^0\overline{Z_nh})
 +\sum_{n,m}w_nw_m Z_nf\,\overline{Z_mh}\biggr]\\
&+i\eta\sum_n w_n(F_f\overline{Z_nh}-Z_nf\overline{F_h})\biggr\}dx.
\end{split}
\tag{14}
\]

These are compressed multiplier pairings and cross-prime products, not scalar atoms already known to have coefficient one. Moreover omega and eta themselves contain the full arithmetic X; B_0 is prime-free only as a temporal expression, not as a claim about the full integrand.

There is a decisive support check. Near (t,u)=(log(2)/2,-log(2)/2), both |t| and |u| are smaller than log 2. Neither B_t nor B_u contains any prime step, yet T(t-u) has its -w_2 delta on t-u=log 2 through that neighborhood. Thus the missing atom cannot be produced there just by differentiating an explicit prime hinge of B. The spectral multipliers must participate. This does not refute (OPEN); it refutes that local hinge-only derivation of it.

## 3. Direct evaluation of both time integrations

The following computation is the main new reduction. It leaves spectral integrals but evaluates the Volterra convolutions and all time integrations. Exponential test factors below are used only to transform continuous kernels of established exponential growth, not as unauthorized tests in Weil's criterion.

For p>1/2 set

\[
\kappa_p=p\int_0^\infty e^{-pt}g'(t)dt,
\qquad
\Omega_p=\frac1\pi\int_{\mathbb R}\frac{p\omega(x)}{p^2+x^2}dx,
\]

\[
J_{pq}=\frac1\pi\int_{\mathbb R}x\eta(x)
\left(\frac1{p^2+x^2}-\frac1{q^2+x^2}\right)dx.
\tag{15}
\]

The difference in J_pq must stay inside the integral: no convergence of the two individually unsubtracted Hilbert integrals is assumed. We have

\[
0<\Omega_p<1,\qquad
|J_{pq}|\le\frac{|\log(q/p)|}{\pi}.
\tag{16}
\]

### Lemma 4: the Laplace input is explicitly arithmetic [ABSTRACT][PAPER]

For s=p+1/2>1,

\[
\boxed{
\kappa_p=-\frac1{p-1/2}-\frac1{p+1/2}
+\frac12\log\pi-\frac12\psi_{\rm d}(s/2)
+\sum_{n\ge2}\frac{\Lambda(n)}{n^s}
=-\frac{\xi'(s)}{\xi(s)}.}
\tag{16a}
\]

**Proof.** Integrate (5). The pole term gives -2p/(p^2-1/4); each prime step gives w_n*exp(-p ell_n). The Lerch integral is an absolutely convergent positive series. With alpha=1/4 and beta=1/4+p/2,

\[
\sum_{j\ge0}\frac1{(j+\alpha)(p+1/2+2j)}
=\frac{\psi_{\rm d}(\beta)-\psi_{\rm d}(\alpha)}p.
\]

Thus its contribution is -[psi_d(beta)-psi_d(alpha)]/2. Use psi_d(1/4)=-gamma_E-pi/2-3log2 and c_A+psi_d(1/4)=log pi. The Euler product logarithmic derivative is absolutely convergent at s>1 and yields the final equality. This calculation involves no zeta zeros. QED.

The strict bounds in (16) follow from (1) and nonconstancy of X. The J bound follows by |eta|<=1/2 and

\[
\int_0^\infty x\left|\frac1{p^2+x^2}-\frac1{q^2+x^2}\right|dx
=|\log(q/p)|.
\]

### Lemma 5: exact double-Laplace Gram formulas [ABSTRACT][PAPER]

Define, for K_N=K_norm^sgn,

\[
\mathcal L_{++}K(p,q)=\int_0^\infty\!\int_0^\infty
 e^{-pt-qu}K(t,u)\,dt\,du,
\]

and L_+- by K(t,-u) in the same integral. Write a=kappa_p and b=kappa_q only in the next formulas. Then

\[
\boxed{
\mathcal L_{++}K_N=
\frac{2+(ab-1)(\Omega_p+\Omega_q)+(b-a)J_{pq}}
 {pq(p+q)}.}
\tag{17}
\]

For p!=q,

\[
\boxed{
\mathcal L_{+-}K_N=
\frac{(1+ab)(\Omega_p-\Omega_q)+(a+b)J_{pq}}
 {pq(q-p)}.}
\tag{18}
\]

All diagonal p=q limits are continuous limits, not omitted parameters.

**Proof.** The existing bound

\[
\|S_t\|_2\le N(|t|),\quad
N(T)=\sqrt{2\pi}\bigl(\sqrt T+\|g'\|_{L^2(0,T)}\bigr)
\le C(1+T)e^{T/2}
\tag{19}
\]

makes the time integrals Bochner-integrable for p>1/2. Their exact values are

\[
\int_0^\infty e^{-pt}S_t(x)dt
 =\frac{\alpha(x)-i\kappa_p\beta(x)}{p(p+ix)},
\quad
\int_0^\infty e^{-pt}S_{-t}(x)dt
 =\frac{-\alpha(x)-i\kappa_p\beta(x)}{p(p-ix)}.
\tag{20}
\]

These follow directly by integrating (2). Products of these L2 functions are L1, so Fubini is justified. For ++ their numerator is
`1+(ab-1)omega+i(b-a)eta`; for +- it is `-1+(1+ab)omega+i(a+b)eta`.
Use

\[
\frac1{(p+ix)(q-ix)}=
\frac1{p+q}\left(\frac1{p+ix}+\frac1{q-ix}\right),
\]

and the analogous difference with denominator q-p for (p+ix)(q+ix). Evenness of omega and oddness of eta give precisely (15); the free integrals are 2pi/(p+q) and zero, respectively. The subtracted eta integrals are absolutely convergent before partial fractions; symmetric truncation preserves their cancellation. This proves (17)-(18). QED.

### Lemma 6: comparison with the full arithmetic target [ABSTRACT][PAPER]

For K_A(t,u)=g(t-u)-g(t)-g(u),

\[
\mathcal L_{++}K_A=-\frac{a+b}{pq(p+q)},\qquad
\mathcal L_{+-}K_A=\frac{a-b}{pq(q-p)}.
\tag{21}
\]

**Proof.** Integration by parts gives integral_0^infinity exp(-pt)g(t)dt=kappa_p/p^2. Split the ++ integral at t=u; for +- put r=t+u. The resulting geometric integrals give (21), including the anchored subtractions. QED.

In particular, **the eta term in (17) is zero at p=q**. For the omega contribution to V alone, its double Laplace value is

\[
\mathcal L_{++}V_\omega(p,p)
=\frac{(\kappa_p^2-1)\Omega_p}{p^3},
\qquad \mathcal L_{++}V_\eta(p,p)=0.
\tag{22}
\]

The causal mixed derivative therefore has equal-parameter Laplace value
`(kappa_p^2-1)Omega_p/p`. The requested right side T(t-u)-2delta(t-u) has value `-(kappa_p+1)/p`. Boundary axes cause no extra terms: V vanishes on both axes, and these derivatives can equivalently be defined after extending the continuous kernel by zero to the positive quadrant.

The target prime part alone has transform

\[
-\frac1p\sum_{n\ge2}\frac{\Lambda(n)}{n^{p+1/2}}<0.
\tag{23}
\]

Consequently V_eta cannot, by itself, have mixed derivative equal to that prime distribution. This is an exact analytic failure of the proposed allocation, not a numerical test and not a refutation of the combined signed identity.

## 4. The exact remainder and the remaining scalar integral

For zeta define

\[
r_p=\Omega_p-\frac1{1-\kappa_p},\qquad
h_{pq}=J_{pq}+\Omega_p-\Omega_q.
\tag{24}
\]

The denominators are legitimate. The canonical positive even theta density represents F(p)=X(ip)=xi(1/2+p) as an exponential moment. Thus F>0, F'>0 for p>0 and

\[
\kappa_p=-F'(p)/F(p)<0,\qquad
\kappa_p'=-\operatorname{Var}_p(t)<0.
\tag{25}
\]

Here the probability density is the normalized positive theta density times exp(pt). Its nonzero variance follows from its positive support on intervals. This uses no assertion about zeros.

Let D=K_N-K_A. Subtraction and elementary algebra in (17)-(21) give the **fully explicit transforms of the continuous kernel remainder**:

\[
\boxed{
\mathcal L_{++}D=
\frac{(a-1)(b+1)r_p+(b-1)(a+1)r_q+(b-a)h_{pq}}
 {pq(p+q)}.}
\tag{L++}
\]

\[
\boxed{
\mathcal L_{+-}D=
\frac{(1-a)(1-b)(r_p-r_q)+(a+b)h_{pq}}
 {pq(q-p)}.}
\tag{L+-}
\]

Both have their limiting values at p=q. For real spectral x, A_(-t)=-conjugate(A_t), B_(-t)=conjugate(B_t), while omega is even and eta is odd in x. Substitution in the Gram integral proves K_N is real symmetric and K_N(-t,-u)=K_N(t,u); the same holds for K_A. Thus these two transforms determine all four quadrants. Uniqueness of the double Laplace transform applies, by (19) and the analogous bound on g.

This is not a free error function: a,b are the absolutely specified arithmetic values (16a), and r,h are the absolutely convergent real-axis integrals (15),(24). In particular

\[
|r_p|\le1,\qquad |h_{pq}|\le1+\frac{|\log(q/p)|}{\pi}.
\tag{26}
\]

These are existence bounds, not vanishing estimates.

### Lemma 7: the full signed identity reduces exactly to one scalar Poisson calculation [ABSTRACT][PAPER]

The following are equivalent for the objects fixed here:

1. (OPEN) in D'(R^2).
2. K_N=K_A on R^2.
3. For every p>1/2,

\[
\boxed{
\frac1\pi\int_{\mathbb R}
\frac{p\,X(x)^2}{(p^2+x^2)(X(x)^2+X'(x)^2)}dx
=\frac{\xi(1/2+p)}{\xi(1/2+p)+\xi'(1/2+p)}.}
\tag{P}
\]

**Proof.** For 1 <=> 2, D has zero mixed derivative exactly when it is a sum of a distribution in t and a distribution in u. Since D is continuous and zero on both axes, it is zero. This can also be proved by mollification and integration over rectangles.

For 2 => 3, put p=q in (17),(21). We obtain

\[
(\kappa_p^2-1)\Omega_p=-(\kappa_p+1).
\]

Away from kappa_p=-1 this gives Omega_p=1/(1-kappa_p). By (25) the exceptional value occurs at most once, and continuity supplies it too. This proves (P).

For 3 => 2, it remains to justify h_pq=0, not assume it. For Re p>0 the same integral

\[
\Omega(p)=\frac1\pi\int_{\mathbb R}
\frac{p\omega(x)}{p^2+x^2}dx
\tag{27}
\]

is holomorphic; the symmetrized integrand is O(x^-2) locally uniformly in p. If (P) holds on the positive ray, analytic continuation gives

\[
(F+F')\Omega=F\quad\text{on Re }p>0.
\tag{28}
\]

This is continuation of an analytic identity, not a contour closure through unknown poles. On the boundary p=iy, the quotient F/(F+F') equals
`X(y)/(X(y)-iX'(y))=omega(y)+i eta(y)`; common real zeros are removable. On the other hand the Cauchy integral (27), with the symmetric tail prescription justified by evenness of omega, has boundary value

\[
\omega(y)-i\mathcal H\omega(y),\qquad
\mathcal H\omega(y)=\frac1\pi\operatorname{PV}\int
                   \frac{\omega(x)}{y-x}dx.
\]

Local existence follows from the smooth removable real-axis multipliers; pairing x and -x makes the tail O(x^-2). Hence eta=-H omega.

Let P_p(x)=p/[pi(p^2+x^2)] and Q_p(x)=x/[pi(p^2+x^2)]. Direct Fourier transformation, or a rational contour integral, gives H Q_p=-P_p. Skew-adjointness of H then gives

\[
J_{pq}=\langle-\mathcal H\omega,Q_p-Q_q\rangle
       =\langle\omega,-P_p+P_q\rangle
       =\Omega_q-\Omega_p.
\tag{29}
\]

This use of Hilbert duality is legitimate by symmetric regularization: Q_p-Q_q=O(x^-3), H(Q_p-Q_q)=-P_p+P_q=O(x^-2), omega is bounded, and the boundary identity has made H omega=-eta bounded. Thus both pairings converge and cutoff boundary terms vanish. Consequently h_pq=0. Now (L++),(L+-) vanish, and Laplace uniqueness gives D=0. QED.

**Status of the lemma:** the equivalence is proved; (P) is NOT proved. It is the remaining literal integral evaluation, not a new weaker premise or a claimed independent supplier. Equations (17)-(29) are mathematical work beyond the parent remainder; they do not supply its missing zero value.

### Exact distribution and local budget

The unreproduced distribution, with the sign matching LHS minus RHS of (OPEN), is

\[
\begin{split}
\mathfrak R={}&\partial_t\partial_u V_{\rm sgn}-T(t-u)+2\delta(t-u)\\
={}&\partial_t\partial_u V_{\rm sgn}
+\tfrac12\operatorname{Pf}\frac1{|t-u|}
+(\gamma_E+\log(2\pi)+2)\delta(t-u)\\
&+\sum_{n\ge2}w_n[\delta(t-u-\ell_n)+\delta(t-u+\ell_n)]
-r_*(t-u)\,dt\,du
=\partial_t\partial_u D.
\end{split}
\tag{30}
\]

The pullbacks under t-u are understood distributionally. For zeta_test in C_c^infinity((-T0,T0)^2),

\[
|\langle\mathfrak R,\zeta_{\rm test}\rangle|
\le\left(\frac{N(T_0)^2}\pi+4G(2T_0)\right)
       \|\partial_t\partial_u\zeta_{\rm test}\|_1,
\quad G(R)=\max_{|r|\le R}|g(r)|.
\tag{31}
\]

This follows by boundedness of the continuous primitive D, not by an assumed Fourier decay of T. The derivative of V alone has bound
`(N(T0)^2/pi+2T0)||partial_t partial_u zeta_test||_1`, as clarified in the parent readback. Equations (L++),(L+-) specify this same remainder by scalar integrals; (31) supplies its local distributional budget. None of the singular target terms in (30) is declared absent from the remainder.

## 5. Where direct evaluation stalls; why this is not an averaging trick

The scalar integrand in (P) is nonnegative and absolutely integrable. Its integral is an ordinary Poisson average of omega, while the asserted right side is the value of a particular meromorphic continuation. Boundary reality/unitarity alone does not identify those two objects.

Concretely, (P) says that the analytic function (27) agrees with F/(F+F'). Setting the real boundary values of that quotient equal to omega is insufficient: poles or a non-Poisson analytic contribution inside the half-plane must be excluded. Dropping such a contribution in a contour computation is the unproved step. It cannot be justified here by saying Theta is inner, or by Proposition 4.1's orthonormal basis.

There is an exact check of the strength of this missing calculation. For Re p>0,

\[
\Re\frac{p}{p^2+x^2}
=\tfrac12\Re\left(\frac1{p-ix}+\frac1{p+ix}\right)>0,
\]

so Re Omega(p)>0. If (28) held and F had a zero p0 in that half-plane, write F=(p-p0)^m h, h(p0)!=0. Dividing (28) by (p-p0)^(m-1) and evaluating at p0 yields `m h(p0)Omega(p0)=0`, impossible. Thus a proof of (P) would exclude all nonreal upper zeros of X. This is a consequence of the attempted integral calculation, not an assumption used to evaluate it.

We did not stop because this consequence is RH. We computed the time integrals, the arithmetic Laplace input, both sign quadrants and the dispersion relation. The actual stall is the unevaluated integral (P). Neither its value nor vanishing of (30) follows from the estimates obtained here.

## 6. Exact plants — 1(d)

Use H1,H2 with their own g_H, P^H and real-axis multipliers as fixed in [P, section 7]; do not retain zeta's prime formula after replacing X. Their signed constructions have the same Volterra algebra. Their explicit zero descriptions give g_H' in L2_loc with exponential growth below exp(t/2), so the local Gram construction and the p>1/2 transforms exist. For H2's sinc product, the individual real-lattice contributions to g_H' have bounds proportional to 2^-j, a summable series; the displaced cos-lattice adds a locally bounded exponential term.

**H1=(1+16z^2)cos(8z).** Put F_H(p)=H1(ip). It has a simple zero p0=1/4 in Re p>0. Its Poisson integral Omega_H, formed from H1^2/(H1^2+H1'^2) on the real axis, has strictly positive real part there. Consequently the analogue of (28) cannot hold. In particular, the analogue of (P) cannot hold for every real p>1/2. This localizes the failing step without a numerical evaluation.

**H2=B(z)(2+cos4z).** Use the explicit B from [P], the product of sinc(2^-j z). At

\[
\delta=(\pi+i\operatorname{arcosh}2)/4,
\qquad p_0=-i\delta,
\]

we have Re p0>0, a simple zero of F_H and no zero of B there. The same positive-real-part argument refutes (28) and hence (P) for this plant.

These are not statements that a root-free proof for arithmetic X is impossible. They show why the Poisson reconstruction step must distinguish the actual arithmetic function from the plants.

For completeness the source's exact compact tests still give a quantitative witness for the full distributional identity. If Z is a compact smooth Fourier transform, with Z(delta)=Z(bar(delta))=0 and both simple, set

\[
V(z)=Z(z)\left[\frac1{Z'(\delta)(z-\delta)}
              -\frac1{Z'(\bar\delta)(z-\bar\delta)}\right].
\tag{32}
\]

For H1 choose Z=H1 times the transform of an even nonnegative smooth bump; for H2 take Z=H2. Division by each vanishing linear factor preserves a compact smooth inverse transform: solve `(i partial_t-alpha)u=h` by
`u(t)=-i exp(-i alpha t) integral_(-infinity)^t exp(i alpha s)h(s)ds`; the vanishing full integral ensures compact support. Thus V is the transform of an actual compact smooth v. Its values at the selected pair are 1,-1 and at all other zeros of H are zero. Therefore

\[
Q_H(v)=-2,\qquad
\langle\mathfrak R_H,v(t)\overline{v(u)}\rangle
=\pi^{-1}\|\widehat{\mathcal P}^{H,\rm sgn}_{Dv}\|_2^2+2\ge2.
\tag{33}
\]

The matching of the kernel norm with this tensor pairing uses the real-axis symmetry of S; it is not an RH-dependent Parseval expansion. The two-dimensional conjugate-zero form is indefinite, while the constructed Gram form is positive. In the direct computation that mismatch is precisely the failure of (P)/(28), not a removable overall factor.

## 7. Radical consistency — 1(e)

Let f0, chi_R and a_q be the exact canonical objects of the parent, psi_R=chi_R U_q f0, and e_R=(1-chi_R)U_q f0. Define

\[
\epsilon_{q,R}=(M_1+2M_0)\int_{|t|\ge R}
 N(|t|)\exp(-a_qe^{2|t|})dt\longrightarrow0.
\]

The signed zero-expansion check [P, (26)-(27)] gives

\[
\|\widehat{\mathcal P}^{\rm sgn}_{D\psi_R}\|_2
\le\epsilon_{q,R}.
\tag{34}
\]

Its proof uses the unconditional all-zero expansion and the exact canonical Fourier identity, not the reality of any zero: the integral of every term is a multiple of X(gamma)=0. The double-exponential envelope and sum m_gamma/|gamma|^2 justify the interchange at each nonexceptional real spectral point; the Bochner bound (19) then gives (34). This auxiliary confirmation is not labelled a zero-sum-free proof of the main norm identity.

By radical membership and the source control-space bound,

\[
|Q(\psi_R)|=|Q(e_R)|\le C_{\mathcal X}\|e_R\|_{\mathcal X}^2.
\]

Our remainder therefore satisfies the explicit consistency estimate

\[
\boxed{
|\langle\mathfrak R,\psi_R(t)\overline{\psi_R(u)}\rangle|
\le\epsilon_{q,R}^2/\pi+C_{\mathcal X}\|e_R\|_{\mathcal X}^2
\longrightarrow0.}
\tag{35}
\]

Thus the calculation preserves the required radical check. It does not infer global equality from convergence on these special tests.

## 8. Constants and the unproved final assembly — 1(f)

The convention ledger is unchanged:

| Quantity | Exact meaning |
|---|---|
| 1/pi | K_N=(1/pi) integral S_t conjugate(S_u) dx. |
| 2 delta(t-u) | Mixed derivative of |t|+|u|-|t-u|; no anti-diagonal delta for signed time. |
| c_0=gamma_E+log(4pi) | Constant in the regularized archimedean correlation formula. |
| c_A=gamma_E+log(8pi)+pi/2 | Constant in the positive difference-energy formula for the Weil form. |
| -(gamma_E+log(2pi))delta_0 | Delta coefficient of T in the finite-part scale fixed below. |
| -w_n at each +/-log n | Atom of T; g'' has +w_n, Q has -2w_n C_psi(log n), DOM has +w_n E_s(log n). |
| d_A=c_A-4 | Constant of the separate mean-density regrouping; not a replacement for the delta coefficient. |

The finite part means

\[
\langle\operatorname{Pf}(1/|t|),\varphi\rangle
=\lim_{\varepsilon\downarrow0}
\left[\int_{|t|>\varepsilon}\frac{\varphi(t)}{|t|}dt
+2\log\varepsilon\,\varphi(0)\right].
\]

Changing this scale changes the delta term and is not allowed silently. The coefficient in (16a) was checked by the same digamma value that fixes c_A; no fitted constant is used.

If (P) were independently proved, Lemma 7 would give (OPEN), then K_N=K_A. For every complex compact smooth psi, justified integration by parts and the bounded Bochner construction would give

\[
Q(\psi)=\langle T(t-u),\psi(t)\overline{\psi(u)}\rangle
=\pi^{-1}\|\widehat{\mathcal P}^{\rm sgn}_{D\psi}\|_2^2\ge0.
\]

The published Weil criterion then gives RH. On psi=f0*s this is exactly DOM=||Tcal s||^2 with Tcal=pi^(-1/2)P_hat^sgn D M_f0. Smooth positivity of f0 makes this substitution cover every compact smooth test. These are conditional concluding steps. Their sole unevaluated identity (P) remains unevaluated; no conclusion about RH or its negation is made.

## 9. Frozen prediction scoring and independent checks

| Registered event, unchanged | p | Fate | Evidence and scope |
|---|---:|---|---|
| P_OPEN_COMPLETE | 0.02 | REFUTED_AS_BATCH_OUTCOME | No proof of (P) or (OPEN) is obtained. This is not a proof the identity is false. |
| P_OPEN_FINITE_PART_REPRODUCED | 0.45 | NOT_ESTABLISHED | Formula (11) and the other omega term are computed, but their sum has not been evaluated to the finite part and delta constant. |
| P_OPEN_PRIME_ATOMS_REPRODUCED | 0.25 | NOT_ESTABLISHED | (12)-(14) identify the actual shift operators, not coefficient-one target atoms; (23) is a target transform, not its extraction from V. |
| P_OPEN_EXTRA_MULTIPLIER_IS_THE_REMAINDER | 0.55 | NOT_ESTABLISHED_AS_STATED | The exact defects affect the whole arithmetic response. The narrower eta-to-primes allocation is refuted by (22)-(23), but that narrower statement is not substituted for the frozen prediction. |
| P_OPEN_PLANT_NAMES_THE_STEP | 0.80 | CONFIRMED | (28), the Poisson reconstruction, fails at the explicit right-half-plane plant zeros; (33) supplies strict compact-test discrepancies. |

Before independent checking of this document, register:

```yaml
P_OPENSGN_LAPLACE_FORMULAS_INDEPENDENT:
  probability: 0.88
  event: equations_17_18_Lplusplus_Lplusminus_survive_without_sign_or_factor_change
  fate: PENDING
P_OPENSGN_POISSON_DISPERSION_REDUCTION_INDEPENDENT:
  probability: 0.82
  event: Lemma_7_including_the_Hilbert_boundary_argument_needs_no_extra_hypothesis
  fate: PENDING
P_OPENSGN_WEAK_ENDPOINT_DERIVATIVE_INDEPENDENT:
  probability: 0.95
  event: equations_3_6_7_hold_for_both_time_signs_and_the_logarithmic_endpoint
  fate: PENDING
```

These are future verification predictions, not retrospective scoring of the algebra already performed. No numerical experiment, Lean run or Aristotle call occurred.

## 10. One bounded directive and closeout

Independently check (17)-(18), the p=q eta cancellation, and the boundary/Hilbert step (27)-(29). The known real-zero calibration may be the elementary function X(z)=z, for which omega=x^2/(x^2+1), eta=x/(x^2+1), kappa_p=-1/p, Omega_p=p/(p+1), and J_pq=1/(p+1)-1/(q+1); these rational integrals can be checked exactly, not fitted. This is a proposed read-only check, not an executed test or a new source substitution for zeta.

If the check passes, the next mathematical computation is the left side of (P), with exactly those X, X' and Lorentzian weight. Any contour derivation must retain contributions of the meromorphic quotient F/(F+F') until their absence or cancellation is independently proved. Boundary modulus one is not that proof. No new queue item, external paid request or experiment is authorized by this directive.

What became smaller: both time integrations and the signed-quadrant bookkeeping have been evaluated; a single explicit scalar integral identity determines the full kernel. What was rejected: the finite g'(0+) substitution and the literal eta-only prime assignment. What was not proved: any new target finite-part/delta/prime coefficient or the remaining scalar identity. The number of independent RH suppliers has not decreased.

This document contains a mathematical partial calculation, not a claim that locating an equivalent scalar target proves progress toward RH by itself. The definite progress is the evaluated transform formulas, strict allocation falsifier, bounded explicit remainder and preservation of the radical tests. Only the expected verdict document is written; prior verdicts, source definitions, Lean, skills, request text, queue and shared state remain unchanged.
