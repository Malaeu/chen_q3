# STATUS: TRY_SOURCE_RIESZ_SQUARE_WITH_EXACT_RADICAL_AND_SIGN_REMAINDER
```yaml
OPERATIVE_CLASS: TRY_SOURCE_RIESZ_SQUARE_WITH_EXACT_RADICAL_AND_SIGN_REMAINDER
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-08-KERNEL
BOUNDARY_ID: GOAL058_SOURCE_SQUARE_WITH_THE_ZERO_IDEAL_AS_KERNEL
RESULT:
  OVERALL: PARTIAL_WITH_PRECISE_REMAINDER
  Q1: PROVED_ON_CLASS
  Q1a: PROVED_ON_CLASS
  Q1b: PROVED_ON_CLASS
  Q1c_PROPOSED_RH_OBSTRUCTION_TO_SOURCE_KERNEL: ATTEMPT_REFUTED_WITH_EXACT_COUNTEREXAMPLE
  Q2: PROVED_ON_CLASS
  Q3: PARTIAL_WITH_PRECISE_REMAINDER
REQUEST_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  COMMIT: bb2a33369e7efbeb96312177e57678967370aa21
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_KERNEL_2026-09-08.txt
  GIT_BLOB: 81ac0016210a61c2171f2c9fbe187d3066205b37
  SHA256: deb9d2dca71b6531ef0432a1f56faf2fcb9c9a6e619cae5bee12b420b87266bb
  BYTES: 12832
  LINES: 68
  FINAL_LF: true
  GITHUB_CONNECTOR_FETCHED: true
  HASHES_AND_COUNTS_INDEPENDENTLY_RECOMPUTED: true
  ALL_CHECKS_MATCH: true
BOOTSTRAP:
  PATH: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
  REF: rh_clean
  GIT_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_SECOND_EXPRESSION
  SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
  TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false
DECISIONS:
  SOURCE_DEFINED_NONTRIVIAL_SQUARE_EXISTS: true
  KERNEL_EQUALS_POINTWISE_ZERO_IDEAL: true
  DOMAIN: explicit_exponentially_weighted_logarithmic_energy_completion_section_2
  SQUARE_TRANSLATION_COVARIANCE_CLAIMED: false
  BOUNDED_ON_THAT_COMPLETION: true
  NONTRIVIAL_CLOSABLE_VERSION_ON_ORDINARY_GLOBAL_L2: impossible_with_the_required_null_translates
  DIVISIBILITY_BY_XI_EQUALS_POINTWISE_VANISHING: not_asserted_without_multiplicity_and_space_conditions
  RADICAL_EQUALS_POINTWISE_ZERO_IDEAL_WITHOUT_RH: proved_on_the_stated_completion
  CALIBRATED_REMAINDER_NONNEGATIVE_IFF_WEIL_POSITIVITY: true
  CALIBRATED_REMAINDER_NONNEGATIVE: not_proved
  ARBITRARY_FIXED_CORRECT_KERNEL_SQUARE_HAS_RH_EQUIVALENT_REMAINDER: NOT_A_VALID_GENERAL_INFERENCE
  FINITE_FIXED_S_SONIN_GLOBAL_MINORANT: refuted_by_compact_source_witnesses
  SUPPORT_DEPENDENT_FINITE_S_MINORANTS_ALL_REFUTED: false
  SEMILOCAL_PROBE_NUMBERS_INTERVAL_RATIFIED: false
  PLUS_CHANNEL_ASYMPTOTIC_IDENTIFIED_BY_THIS_PROBE: false
  ALL_N_SIGN_PROVED: false
CLOSES: [REQ-2026-09-08-KERNEL]
CLOSED_RESEARCH_QUESTIONS:
  - source_kernel_existence_on_a_specified_completion
  - topology_and_multiplicity_ambiguities_in_the_zero_ideal
  - finite_fixed_S_reservoir_null_family_discriminator
  - ALIGN_CC20_pole_null_criterion_citation_check
CLOSES_ANALYTIC_RH_SUPPLIERS: []
OPENS: []
UNCHANGED_OPEN_ATOM: ALL_SUPPORT_SIGNED_SCHUR_HEAD_LOWER_BOUND
NEW_DERIVATIONS:
  SCOPES: [ABSTRACT, COFINAL_FAMILY]
  VERIFIER: PAPER
  INDEPENDENT_REVIEW: pending
  LEAN_KERNEL_VERIFIED: false
EXECUTION:
  HASH_COMPUTATION: true
  NUMERICAL_RUN_PERFORMED: false
  INTERVAL_CERTIFICATE_RERUN: false
  LEAN_EDIT: false
  ARISTOTLE_SUBMISSION: false
  QUEUE_OR_STATE_EDIT: false
PUBLICATION:
  AUTHORIZED_WRITE_SCOPE: VERDICT_DOC_ONLY
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_KERNEL_2026-09-08.md
  OLD_ARTIFACTS_OVERWRITTEN: false
  COMMIT_AND_READBACK_HASH: delivery_receipt
  COMMIT_IS_NOT_MATHEMATICAL_VALIDATION: true
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## 0. Decision and evidence boundary

**A nontrivial source-defined positive square with exactly the pointwise zero ideal as kernel exists without RH. Its existence does not settle the sign.** On the explicit completion below, let \(A\) be the Riesz representative of the full, signed, geometric Weil form in an independently positive reference metric. Then
\[
 X=A/\sqrt{22},\qquad
 R[f]=\langle f,(A-A^2/22)f\rangle,
 \qquad Q[f]=\|Xf\|^2+R[f].                         \tag{K1}
\]
The definition uses all source prime coefficients and the archimedean energy, not a list of zeros, an assumed positive Weil form, or a square root of a Schur head. A proof below identifies \(\ker A=\mathcal N\). For this calibrated construction, \(R\ge0\) is equivalent to the unchanged Weil sign. It has **not** been proved. This answers the object question but is not a new positivity mechanism. [ABSTRACT][PAPER]

There are two important qualifications. First, on ordinary global \(L^2(dx)\), no nonzero closable operator can have a kernel containing all translates of the given null test. Second, vanishing at every distinct zero is not the same as divisibility with the zero's full multiplicity. The request does not specify its completion and conflates these two ideals. Sections 1--3 resolve both points explicitly, rather than silently choosing a convenient meaning. [ABSTRACT][PAPER]

The finite-S diagnosis has a rigorous repair: injectivity of convolution by the theta null test and nontriviality of the Sonin space yield a strict negative upper witness for the *global minorant* on compact pole-null tests. Floating-point numbers are unnecessary for that argument. This kills a fixed finite-S minorant, not every support-dependent finite-S construction, and not the full Weil sign. [COFINAL_FAMILY][PAPER]

**Source keys.** [REQ] is the byte-exact request in the header. [ALIGN] is the pinned ALIGN verdict, blob `7c6841aa0d8a575a5fcee9fe03d5ae37e316c997`, SHA-256 `f6edb6d03bf719a830607fa130bbfe9b2a0842eae0b21ac6a1d2f17c5eadc832`; its supplied local file was read. [AC] is `docs/routeB_bus/ALIGN_INDEPENDENT_CHECK_2026-09-08.md`, blob `133a63b2996c30e384a3c873dbdb0b920b69bd0a`. [NP] is `docs/routeB_bus/NEAR_NULL_PROBE_OF_THE_SONIN_FLOOR_2026-09-08.md`, blob `0c5bf5d2f413603514e7c34c2b9c2d616299eb6d`. [SF] is the SCALARFLOOR verdict, Theorem 1 and equations (4)--(7), (14). [C] is COMPENSATE, particularly (1), (28)--(31), (39)--(42). [LM] is the named literature map. These repository readings use the request commit unless another immutable pin is stated. AC/NP numerical reports are reported diagnostics, not interval certificates. Old exported conversations are not definition sources.

Primary papers are read directly at the locators in Section 4. No claim of historical priority is made for Riesz representation, operator squaring, quotient factorization, or the signed explicit formula. The new contribution of this verdict is their exact domain, source, kernel and sign accounting for this request.

## 1. The exact ideal, and three invalid implications in the request

All claims in this section are [ABSTRACT][PAPER]. Put
\[
 F_f(z)=\int_{\mathbb R}f(x)e^{zx}\,dx,
 \quad \Lambda_\xi(z)=\xi(1/2+z),
 \quad \Xi(t)=\Lambda_\xi(it).
\]
Here \(\Lambda_\xi\) is not the von Mangoldt function. Let \(Z_c\) be the set of **distinct** zeros of \(\Lambda_\xi\), with multiplicities \(m_\lambda\), and \(j\lambda=-\overline\lambda\). We use the request's centered convention, not zeros of \(\xi\) inserted into an uncentered Laplace transform.

### 1.1 Point values, multiplicities, and growth

On the completion \(\mathscr H\) defined in Section 2 the formal pointwise ideal is
\[
 \mathcal N_{\rm pt}
 =\{f\in\mathscr H:F_f(\lambda)=0\ (\lambda\in Z_c)\}.   \tag{K2}
\]
The analytic quotient condition instead requires
\[
 F_f^{(r)}(\lambda)=0\quad(0\le r<m_\lambda),              \tag{K3}
\]
plus any growth conditions imposed on \(F_f/\Lambda_\xi\). RH alone does not assert simplicity, and growth membership is a further issue. The signed Weil form samples point values with multiplicity as a coefficient; it does not sample these derivatives.

For example, division by \(z^2\) is not implied by vanishing at \(z=0\). More specifically, if \(\Lambda_\xi\) has a zero \(\lambda\) of order at least two, the construction in Section 3 produces the admissible transform
\[
 (z^2-1/4)\Lambda_\xi(z)/(\lambda-z).
\]
It vanishes at every distinct zero but lacks one order at \(\lambda\). This is a conditional separation if a multiple zero exists, not a claim that one exists. Thus the exact kernel proved here is (K2), as formally defined by the request. The stronger multiplicity/growth ideal is not substituted for it. The word ideal here denotes the stated vanishing subspace; we do not assert that the reference Hilbert space itself is a Banach convolution algebra.

### 1.2 What a positive remainder actually forces

If \(Q[f]=\|Xf\|^2+R[f]\) and \(R\ge0\) on a domain containing a \(Q\)-null vector \(g\), then \(Xg=0\) and \(R[g]=0\). Accordingly,
\[
 \mathcal N_{\rm pt}\subseteq\ker X                       \tag{K4}
\]
is necessary on the common domain. **Equality is not necessary.** The example \(X=0, R=Q\), considered conditionally when \(Q\ge0\), already disproves the proposed logical requirement of equality.

Likewise, annihilating every displayed \(g_k\) implies annihilation of their span and its closure in the relevant graph topology. It does not imply annihilation of all of \(\mathcal N_{\rm pt}\) without a density theorem. No density of the derivative family alone in that ideal is used here. We prove the entire kernel independently in Section 3.

An operator depending on a support index is a different contract. A family \(X_n\) acting only on compact-window domains need not annihilate a noncompact \(g_k\) at each finite n. Its limiting behavior must be specified before (K4) can be used against it.

### 1.3 Same kernel does not calibrate a lower bound

On \(H=N\oplus\mathbb C\), take \(Q[n\oplus z]=|z|^2\) and \(X(n\oplus z)=2z\). Then \(\ker X=N=\operatorname{rad}Q\), but
\[
 R[n\oplus z]=-3|z|^2.                                  \tag{K5}
\]
Consequently, for an **arbitrary fixed** correct-kernel square, positivity of Q need not imply positivity of its remainder. The scale of X matters. The calibrated construction (K1) is deliberately chosen so that the converse does hold. This distinction is also required when scoring the frozen word “any.”

## 2. A source-only positive reference space and a bounded square

All results in this section are [ABSTRACT][PAPER]. The reference metric is fixed before the sign question and has no unknown floor in its definition.

### 2.1 Source convention and reference energy

Set
\[
 A_0(t)=\frac{e^{-t/2}}{1-e^{-2t}},\quad
 c_A=\gamma_E+\log(8\pi)+\pi/2,\quad
 U_tf(x)=f(x-t),\quad w_m=\frac{\Lambda(m)}{\sqrt m}.
\]
The letter A below denotes an operator; \(A_0\) denotes this positive scalar kernel. With antilinear first inner products define
\[
 \mathcal D(f,g)=\int_0^\infty A_0(t)
       \langle U_tf-f,U_tg-g\rangle_{L^2}\,dt,
 \qquad \mathcal W[f]=\int e^{2|x|}|f(x)|^2dx.
\]
The unchanged geometric source is
\[
\begin{split}
 Q(f,g)={}&\mathcal D(f,g)-c_A\langle f,g\rangle
 -\sum_{m\ge2}w_m\{\langle f,U_{\log m}g\rangle
                         +\langle f,U_{-\log m}g\rangle\}\\
 &+\overline{M_+(f)}M_-(g)+\overline{M_-(f)}M_+(g),\\
 M_\pm(f)={}&\int f(x)e^{\pm x/2}dx.                     \tag{K6}
\end{split}
\]
No prime powers or pole terms have been dropped. On compact support the sum is finite by autocorrelation support; the next bounds define it absolutely on a larger space.

Let
\[
 \mathscr E=\{f\in L^2(\mathbb R):\mathcal W[f]+\mathcal D[f]<\infty\},
 \quad \|f\|_{\mathscr E}^2=\mathcal W[f]+\mathcal D[f],
 \quad \mathscr H=\ker M_+\cap\ker M_-\subset\mathscr E. \tag{K7}
\]
The positive Dirichlet form is closed: in Fourier coordinates it is the multiplier with nonnegative symbol
\[
 a(t)=\Re\psi(1/4+it/2)-\psi(1/4),
\]
or equivalently the closed translation-difference form. Adding the closed positive multiplication form \(\mathcal W\) gives a Hilbert norm. The intersection with the two continuous moment kernels is a closed Hilbert subspace.

On every fixed compact interval the weight \(e^{2|x|}\) is bounded above and below, and \(1+a(t)\) is comparable with \(\log(2+|t|)\). Thus (K7) contains the **entire local logarithmic form domain**, not just smooth or H1 tests. It is an explicit global completion of compact pole-null tests. It is not claimed to equal an unspecified unweighted global completion in the request.

**Structure inventory.** The source Q, its complex polarization, physical dx normalization, all prime powers, both total pole constraints, and every compact-support test are preserved. The new reference norm is fixed, explicit and independent of zeros, but it is **not translation-invariant**. Accordingly the square and R are not individually claimed translation-invariant or scaling-equivariant; their sum is the original Q. This is a variational detector, not a new spectral realization with the zeros as eigenvalues. Additional requirements of covariance, an Euler-product factorization of X, or a fast finite evaluator are not proved by (K10).

### 2.2 Core and exact restoration of the two constraints

Here are the domain details needed for that last statement. Choose smooth \(\chi_R\), bounded by one, equal to one on \([-R,R]\), zero outside \([-2R,2R]\), with a uniform Lipschitz bound. Weighted L2 convergence \(\chi_R f\to f\) is dominated convergence. For the Dirichlet part expand
\[
 U_t((1-\chi_R)f)-(1-\chi_R)f
 =(1-U_t\chi_R)(U_tf-f)+(\chi_R-U_t\chi_R)f.
\]
The first term tends to zero in the translation-energy integral by domination by \(\mathcal D[f]\). For the second use
\(|\chi_R(x)-\chi_R(x-t)|\le\min(2,C|t|)\), then dominated convergence with
\(\int A_0(t)\min(4,C^2t^2)dt<\infty\).

Mollify the resulting compact function with a nonnegative smooth approximate identity. In Fourier coordinates its multiplier is bounded by one and tends pointwise to one, so convergence holds in \(\mathcal D\) as well as L2. Supports stay in a fixed slightly enlarged compact interval, giving weighted L2 convergence too.

To restore moments, fix one nonnegative nonzero smooth bump b and its translates by 1 and -1. Their moment columns are
\((e^{1/2}M_+(b),e^{-1/2}M_-(b))^t\) and
\((e^{-1/2}M_+(b),e^{1/2}M_-(b))^t\).
Their determinant is \((e-e^{-1})M_+(b)M_-(b)\ne0\). Subtract their unique linear combination with the two unwanted moments. Its coefficients tend to zero. Thus compact smooth pole-null tests are dense in \(\mathscr H\), with exact, not numerical, constraints. This also supplies the kind of closure argument singled out in [AC].

### 2.3 Absolute source bound, with an explicit rational constant

For all real t,
\[
 |\langle f,U_tg\rangle|
 \le e^{-|t|}\mathcal W[f]^{1/2}\mathcal W[g]^{1/2},
 \qquad |M_\pm(f)|\le\sqrt{4/3}\,\mathcal W[f]^{1/2}.   \tag{K8}
\]
The first follows from \(|x|+|x-t|\ge|t|\) and Cauchy--Schwarz. The second uses \(\int e^{\pm x-2|x|}dx=4/3\). Since
\[
 c_A<7,\qquad \sum_{m\ge2}\frac{\log m}{m^{3/2}}<6,
\]
(K6) gives
\[
\begin{split}
 |Q(f,g)|
 &\le \mathcal D[f]^{1/2}\mathcal D[g]^{1/2}
       +\frac{65}{3}\mathcal W[f]^{1/2}\mathcal W[g]^{1/2}\\
 &\le\frac{65}{3}\|f\|_{\mathscr E}\|g\|_{\mathscr E}
 <22\|f\|_{\mathscr E}\|g\|_{\mathscr E}
 \quad(f,g\ne0).                                      \tag{K9}
\end{split}
\]
Appendix A proves the simple constants. This is an absolute continuity bound, **not a sign estimate**. In particular it uses no RH statement.

### 2.4 The construction and its exact remainder

By the Hilbert-space Riesz theorem there is a unique bounded self-adjoint A on \(\mathscr H\) such that
\[
 \langle h,Af\rangle_{\mathscr H}=Q(h,f),\qquad
 \|A\|\le65/3.                                        \tag{K10}
\]
This is an explicit variational definition from source data. The positive reference solve is (K7); the right-hand side is exactly (K6). There is no invocation of a square root of Q, \(S_n\), or an assumed positive eigenspace. It is not claimed to be a closed-form, seconds-long evaluator. This is an operator square; the quartic expression \(Q[f]^2\) is not used.

Define X and R by (K1), using the \(\mathscr H\) norm. Expansion proves the identity on all of \(\mathscr H\). More precisely,
\[
 B=I-A/22,\qquad \frac1{66}I\preceq B\preceq\frac{131}{66}I,
 \qquad A-A^2/22=B^{1/2}AB^{1/2}.                       \tag{K11}
\]
The square root here is of a **proved uniformly positive reference perturbation**, not the target form. Since A and B commute and B is invertible,
\[
 \boxed{R\ge0\ \Longleftrightarrow\ A\ge0
        \ \Longleftrightarrow\ Q\ge0\text{ on }\mathscr H.} \tag{K12}
\]
In fact (K11) preserves the positive and negative spectral subspaces. The representation cannot erase a negative direction. The compact-core result and the exact pole-null criterion in Section 4 give
\[
 \boxed{R\ge0\text{ on }\mathscr H\ \Longleftrightarrow\ RH.} \tag{K13}
\]
This proves an equivalence, not either side. It explains precisely why (K1), although it answers the kernel-object question, supplies no sign theorem for (A14).

Nontriviality is unconditional. Take a nonzero smooth \(\eta\) in an interval of length \(d=2^{-24}\), and \(f=(\partial_x^2-1/4)\eta\). It is pole-null and nonzero. There are no prime correlations, and the disjoint-translate energy for \(t>d\) gives
\[
 Q[f]\ge\left(2\int_d^\infty A_0(t)dt-c_A\right)\|f\|_2^2
 >\|f\|_2^2.                                          \tag{K14}
\]
Appendix A supplies the rational budget. Hence A and X are nonzero. The assertion that no nontrivial source positive form annihilating the null ideal can exist will be disproved once its exact kernel is identified.

## 3. Exact source kernel without RH; what changes in ordinary L2

All results here are [ABSTRACT][PAPER], except the indexed compact approximations, which also have [COFINAL_FAMILY][PAPER] scope.

### 3.1 The signed explicit formula on the chosen completion

For \(f\in\mathscr E\), \(F_f\) is holomorphic on \(|\Re z|<1\). On \(|\Re z|\le1/2\),
\[
 |F_f(z)|\le\sqrt{4/3}\,\mathcal W[f]^{1/2}.             \tag{K15}
\]
Consequently (K2) is closed. For compact smooth g the full signed explicit formula, polarized in our convention, is
\[
 Q(f,g)=\sum_{\lambda\in Z_c}m_\lambda\,
             \overline{F_f(j\lambda)}F_g(\lambda).     \tag{K16}
\]
Initially take compact smooth f too. This is the unchanged source explicit formula of [ALIGN, (A27)] and [CC20, Appendix B], not a positive zero-side Gram. To extend in f, use the core above, (K15), rapid vertical decay of \(F_g\), and the unconditional zero count \(O(T\log(2+T))\). These give an absolutely summable uniform majorant on the zero set. Source continuity follows from (K9). This proves (K16) for the stated f and g without relocating any zero.

It immediately follows that
\[
 \mathcal N_{\rm pt}\subseteq\operatorname{rad}(Q|_{\mathscr H}). \tag{K17}
\]
This is stronger than mere isotropy \(Q[f]=0\), and it is unconditional.

### 3.2 A separating test at any one zero, with every multiplicity allowed

For completeness, the reverse inclusion does not rely on an unverified interpolation slogan. Use the exact theta function already normalized in [ALIGN, (A22)--(A24)]:
\[
 \Phi(x)=\sum_{m\ge1}(4\pi^2m^4e^{9x/2}-6\pi m^2e^{5x/2})
                           e^{-\pi m^2e^{2x}},
 \qquad F_\Phi(z)=\Lambda_\xi(z).                      \tag{K18}
\]
It is even, smooth, and all derivatives decay doubly exponentially at both ends. The parent derives this from Gaussian Poisson summation; [AC] independently checks the normalization and the signed source convention. No positive-zero-sum formula is imported.

If a doubly exponentially decreasing smooth v satisfies \(F_v(\lambda)=0\), define
\[
 (J_\lambda v)(x)
 =e^{-\lambda x}\int_{-\infty}^xe^{\lambda t}v(t)dt
 =-e^{-\lambda x}\int_x^\infty e^{\lambda t}v(t)dt.       \tag{K19}
\]
The two expressions give decay at the two respective ends. They and the differential equation \((\partial_x+\lambda)J_\lambda v=v\) show that all derivatives retain double-exponential decay, allowing a smaller positive exponential constant. Integration by parts gives
\[
 F_{J_\lambda v}(z)=F_v(z)/(\lambda-z).                  \tag{K20}
\]
If \(\lambda\) has multiplicity r in \(\Lambda_\xi\), apply this operation r times to \(\Phi\). At every stage before the last division the required zero remains. Set
\[
 h_\lambda=(\partial_x^2-1/4)J_\lambda^r\Phi,
 \quad
 F_{h_\lambda}(z)
 =(z^2-1/4)\frac{\Lambda_\xi(z)}{(\lambda-z)^r}.         \tag{K21}
\]
This is an entire transform of an element of \(\mathscr H\). Its values vanish at every other distinct zero, and
\[
 F_{h_\lambda}(\lambda)
 =(\lambda^2-1/4)(-1)^r\Lambda_\xi^{(r)}(\lambda)/r!\ne0. \tag{K22}
\]
The factor is nonzero because \(\xi(0),\xi(1)\ne0\).

Equation (K16) remains valid for this g: approximate by
\((\partial_x^2-1/4)(\chi_RJ_\lambda^r\Phi)\).
These tests are compact and exactly pole-null, converge in \(\mathscr E\), and have uniformly bounded exponentially weighted derivatives of each prescribed finite order. Repeated integration by parts therefore gives the uniform vertical decay needed in (K16). In particular the zero-series limit is dominated, not only pointwise.

If f is in the radical on \(\mathscr H\), test against \(h_\lambda\). The series collapses to
\[
 0=Q(f,h_\lambda)
 =m_\lambda\overline{F_f(j\lambda)}F_{h_\lambda}(\lambda).
\]
Since j permutes the zeros, all \(F_f(\lambda)\) vanish. Together with (K17) and (K10),
\[
 \boxed{\ker X=\ker A=\operatorname{rad}(Q|_{\mathscr H})
                     =\mathcal N_{\rm pt}.}             \tag{K23}
\]
**Zeros were used to prove what the kernel is, not to construct A or X.** The source definition is (K6)--(K10). The auxiliary separating tests need not be known to evaluate that definition. No zero locations are inputs to the square.

A further exact adversarial control checks that this construction has not silently assumed the desired sign. If a zero \(\lambda\) is off the critical line, then \(\lambda\ne j\lambda\). Normalize \(h_\lambda\) and \(h_{j\lambda}\) to take value one at their respective isolated zeros and subtract them. The resulting pole-null test u has transform values 1 and -1 at that pair and zero at every other distinct zero, so (K16) gives
\[
 Q[u]=-2m_\lambda<0.                                   \tag{K23a}
\]
Compact exactly pole-null approximations retain a negative upper value by (K9). This is a conditional witness under an arbitrary off-line zero, not an actual negative zeta test. It confirms directly why a source kernel and signed quotient can exist before their positivity is resolved.

### 3.3 An ordinary-L2 obstruction, unrelated to whether RH holds

Let \(g_0=(\partial_x^2-1/4)\Phi\). Its Fourier transform is
\[
 \widehat g_0(t)=-(t^2+1/4)\Xi(t),                        \tag{K24}
\]
and is nonzero almost everywhere, because \(\Xi\) is nonzero entire. Every translate \(U_bg_0\) is in \(\mathcal N_{\rm pt}\): its Laplace transform gains the zero-free factor \(e^{bz}\), and both pole moments remain zero.

The span of these translates is dense in ordinary \(L^2(dx)\). To prove this, an L2 vector orthogonal to every translate has \(\overline{\widehat g_0}\widehat u\in L^1\) with identically zero inverse Fourier transform. Fourier uniqueness makes that product zero almost everywhere; (K24) makes u zero.

Suppose a closable operator Y from ordinary L2 to any Hilbert space has every \(U_bg_0\) in its domain and kernel. The graph of its closure then contains \((u,0)\) for every L2 vector u by density. Since that graph is single-valued, the closed operator, and hence Y, is zero. Therefore
\[
 \boxed{\text{No nonzero closable ordinary-global-L2 detector
 annihilates all the required null translates.}}         \tag{K25}
\]
This is not an RH-equivalence obstruction. It holds with either truth value of RH. It explains why “take the L2 orthogonal complement of the zero ideal” is the wrong proposal: that ideal is L2-dense. In (K7), by contrast, evaluations are continuous, the ideal is closed and proper, and (K23) gives a nonzero bounded detector. The topology is load-bearing.

### 3.4 Source division and a source projection

Division itself has the wrong kernel. On its legal domain, \(F\mapsto F/\Lambda_\xi\) is injective; it does not annihilate divisible functions. Projecting away the divisibility ideal also requires specifying multiplicities and growth, as in Section 1.

For the pointwise ideal and the fixed positive metric (K7), an unconditional source-only projection is available:
\[
 \Pi_{\mathcal N_{\rm pt}^\perp}
 =s\!\!\lim_{\epsilon\downarrow0}
       A^2(A^2+\epsilon I)^{-1}.                        \tag{K26}
\]
The spectral theorem proves the strong limit and its exact kernel. Every inverse in (K26) is of a proved positive operator bounded below by \(\epsilon I\), irrespective of Q's sign. This is not a quotient constructed by enumerating the zeros. But the projection's norm square need not be a Weil minorant: even a positive Q need not pay one unit of the reference norm on its quotient. The calibrated A-square, not this unit projection, supplies the equivalence (K13).

## 4. First-source adjudication of the four proposed constructions

The descriptions below are **READ** at the stated locators, not inherited from [LM]. They are kept separate from our derivations. All scope assessments are [ABSTRACT][PAPER]; no published theorem is claimed to prove the unpaid sign.

### 4.1 Connes 1999: the cokernel is not an all-zeros positive Sonin square

**READ:** Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta function*, Selecta Math. 5 (1999), arXiv:math/9811068v1. Section III, Theorem 1, p.13: the spectrum represents **critical-line zeros**, with a weight-dependent multiplicity cap. Page 14 says the construction “did not have to define the L functions”; p.15 permits Jordan blocks, not skew-adjointness.

**READ:** Section VIII, (16), Theorem 5, pp.41--42, makes a regularized cutoff-trace asymptotic equivalent to all Hecke RH for the stated positive-characteristic field. The number-field analogue is discussed on pp.46--47, (33). The theorem pages were visually checked. This is neither the unconditional signed explicit formula nor a proved identity \(Q=\|T_fS_{\rm all}\|_{HS}^2+R\ge0\).

**Decision:** its cokernel construction does not supply the requested positive minorant. It does show why source-defined quotient data and prior knowledge of zero locations must not be conflated.

### 4.2 CC20: an actual positive square, with an actual support restriction

**READ:** Connes--Consani, *Weil positivity and Trace formula, the archimedean place*, arXiv:2006.13771v1. Theorem 1, (4), assumes support \([2^{-1/2},2^{1/2}]\) and Fourier vanishing at \(i/2\) and 0. Its Sonin trace is “positive definite by construction.” Section 6.7, Theorem 11, gives a rank-one-corrected version, not unrestricted positivity.

**READ, resolving [AC]'s citation debt:** Appendix C, Proposition 1, (155), permits a finite Mellin-vanishing set containing \(\{0,1\}\) and disjoint from the nontrivial zeros. With \(\widetilde g(s)=F_f(s-1/2)\), this is the compact pole-null criterion used in (K13), with (K6)'s sign.

**Decision:** the local theorem is preserved. Our Section 5 independently shows why its square cannot be extended to a global fixed-reservoir minorant.

### 4.3 CCM23: finite-Euler transport is not an exact all-zero spectrum

**READ:** Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators: Semilocal adelic operators*, arXiv:2310.18423v2. Definition 2.2 is a formal prolate construction; Theorem 3.1 treats the archimedean cyclic representation. Definition 4.5 specifies Sonin spaces. Equations (57)--(58) give finite Euler multipliers; Theorem 4.6 gives a “hilbertian isomorphism” of archimedean and finite-S Sonin spaces. Section 4.8 retains the S-dependent inner product.

These fixed-S multipliers are invertible on the real Mellin line. The transport preserves nontriviality, not an all-zero kernel. No all-places limit or global Weil minorant follows.

**Decision:** this dictionary supports Section 5's nonvanishing test. It does not identify the finite prolate spectrum with all zeta zeros or supply the requested global X.

### 4.4 Connes 2026: the radical is already distinguished from a local square

**READ:** Connes, *The Riemann Hypothesis: Past, Present and a Letter Through Time*, arXiv:2602.04022v1, Section 6.4, (20)--(21). The discussion puts the summation-map range in the global Weil radical and explains truncation as a near-radical construction. Its description uses “contained in the radical,” not equality with a fixed finite-prime Sonin range. Section 6.5, Fact 6.4, concerns the trial limit; Section 6.6 leaves the simple-even minimum and the adequate ground/trial comparison as proof obligations. Section 7 discusses the scaling-site geometric program, not a proved number-field positive intersection form.

**Decision:** these passages support keeping exact null objects separate from local positive reservoirs. They do not supply R's sign in (K1).

### 4.5 Gram/Cholesky and the literature map

The proposed \(X=S_n^{1/2}\) needs positivity of that exact head and therefore cannot supply it. No such square root is used here. Squaring the bounded **signed** operator in (K10) is a different operation and is legal before positivity.

[LM]'s universal statements “only proved SOS” and “de Branges closed structurally” are not adopted. Specific failed de Branges inequalities do not prove the death of every entire-function-space representation. A classification of all source-defined squares would require a defined class of constructions and a theorem. Our construction already disproves emptiness for the broad class specified by [REQ]. We do not import any unread original Weil text or an unverified all-places projector.

## 5. Q2: null-family discriminator, with source proofs instead of numerical signs

### 5.1 A multiplier fact that proves nonvanishing

In the common Mellin model, the tested scaling operator \(T_f\) is the Fourier multiplier \(\widehat f\). Every \(g_k=(\partial_x^2-1/4)\partial_x^k\Phi\) has transform
\[
 \widehat g_k(t)=-(it)^k(t^2+1/4)\Xi(t),                 \tag{K27}
\]
which is nonzero almost everywhere. Hence \(T_{g_k}\) is injective on this L2 representation. For **any nonzero bounded operator C** in that representation,
\[
 T_{g_k}C\ne0.                                         \tag{K28}
\]
Its Hilbert--Schmidt square is strictly positive if finite, and otherwise infinite, not zero. This is independent of the sign of Q. For finite S, the literal Mellin transport in [SF] and [CCM23] is the required common representation; a different global adelic representation would need its own argument. [ABSTRACT][PAPER]

The infinite-dimensional archimedean Sonin space and the finite-S isomorphism in Theorem 4.6 give \(\mathsf S_S\ne0\) for every fixed finite S. Therefore
\[
 T_{g_k}\mathsf S_S\ne0.                               \tag{K29}
\]
The inference does **not** assert that a nonnegative density is positive everywhere. It uses a nonzero operator and an injective multiplier. A nonzero absolutely continuous nonnegative multiplier form also cannot annihilate \(g_0\): (K24) would force its density to be zero almost everywhere.

### 5.2 A strict compact witness against the fixed-S global minorant

Choose a unit \(\psi\) in the Sonin range and put \(a_S=\|T_{g_0}\psi\|^2>0\). Let
\[
 g_{0,R}=(\partial_x^2-1/4)(\chi_R\Phi).
\]
These are compact smooth and exactly pole-null; they converge to \(g_0\) in \(\mathscr E\) and L1. Thus \(Q[g_{0,R}]\to0\), by (K23) and (K9), while \(T_{g_{0,R}}\to T_{g_0}\) in operator norm. For every R,
\[
 Q[g_{0,R}]-\|T_{g_{0,R}}\mathsf S_S\|_{HS}^2
 \le Q[g_{0,R}]-\|T_{g_{0,R}}\psi\|^2.                  \tag{K30}
\]
For all sufficiently large R the right side is strictly below \(-a_S/2\): take \(|Q[g_{0,R}]|<a_S/4\) and \(\|T_{g_{0,R}}\psi\|^2>3a_S/4\).

This is the required **negative upper witness**, on actual compact tests, to
\(Q\ge n_S\) for each **fixed finite S** on all supports. It does not require an unproved global HS extension at \(g_0\), or the decimal n2 values in [NP]. If a compact sandwich were infinite, the asserted finite minorant would fail a fortiori. A uniform argument for a varying \(S=S(R)\) does not follow: \(a_S\) and the entrance R may depend on S. Local finite-S theorems are not contradicted. [COFINAL_FAMILY][PAPER; KILL_SCOPE=THEOREM_SHAPE]

### 5.3 The correction square does not repair its own null kernel

For the literal cutoffs, \(D_S=P+Q_S-I+\mathsf S_S\) and
\[
 PD_SP=PQ_SP=(PF_SP)^*(PF_SP)\quad\text{on ran }P.       \tag{K31}
\]
Thus a nonzero cutoff overlap gives \(D_S\ne0\). For the archimedean cosine transform that overlap is immediate from its nonzero kernel. For the relevant \(S=\{\infty,2\}\) it follows directly from [SF]'s Euler formula, without conditioning calculations. If b is the cosine transform of a nonnegative smooth function supported compactly in \((0,1)\), then b is Schwartz and \(b(0)>0\). In the positive-variable unitary dilation convention the formula becomes
\[
 F_2h(u)=\tfrac12\sum_{j\ge0}b(2^ju)-\tfrac12 b(u/2)
       =\frac{b(0)}{2\log2}\log(1/u)+O(1)\quad(u\downarrow0). \tag{K32}
\]
To verify the last estimate, split the sum at \(j=\lfloor\log_2(1/u)\rfloor\); the errors before it are bounded by a geometric sum using \(b(s)-b(0)=O(s)\), and the Schwartz tail afterwards is bounded. Thus \(PF_2P\ne0\), so \(D_2\ne0\).

The same argument works for any fixed finite prime set: the product of the finite-Euler factors has a leading term
\[
 b(0)\frac{\prod_{p\in S_f}(1-p^{-1})}
                 {r!\prod_{p\in S_f}\log p}
             (\log(1/u))^r,
 \quad r=|S_f|,                                        \tag{K33}
\]
and lower degree errors. Indeed the nonnegative lattice count \(\sum j_p\log p\le L\) equals \(L^r/(r!\prod\log p)+O((1+L)^{r-1})\) by comparing unit boxes with the simplex. Replacing b by b(0) inside that simplex costs only boundary slabs; the Schwartz tail costs the same order. Terms choosing a finite dilation instead of a geometric sum have smaller degree. The r=0 case is the archimedean overlap itself.

Equations (K28) and (K31)--(K33) prove \(T_{g_k}D_S\ne0\). The rank-one argument (K30), with any unit \(\psi\) satisfying \(D_S\psi\ne0\), also rules out its HS square as a global minorant by itself. The bare \(D_S\) is **not** asserted Hilbert--Schmidt. [ABSTRACT/COFINAL_FAMILY][PAPER]

### 5.4 Complete classification of the named squares

“Does not vanish on N” means there is an explicitly specified member of N on which it is nonzero; it does not mean every member has positive value.

| Candidate | Vanishes on the entire pointwise ideal? | Exact reason and scope |
|---|---|---|
| Fixed finite-S Sonin square \(n_S(f)\) | No | (K27)--(K30), including the archimedean case; nonzero or infinite at \(g_k\). ABSTRACT/COFINAL_FAMILY, PAPER. |
| Correction \(\|T_fD_S\|_{HS}^2\) | No | (K31)--(K33), injectivity, then the same compact rank-one witness. ABSTRACT/COFINAL_FAMILY, PAPER. |
| CC20 \(\operatorname{Tr}(\vartheta(g)S\vartheta(g)^*)\) | No, under the literal logarithmic dictionary | It is the archimedean row above. Its *local lower-bound theorem* has a different support domain and is preserved. ABSTRACT, PAPER. |
| Pole square \(2|M_c|^2\) | Yes | It vanishes on all of \(\mathscr H\), hence is the zero form on this domain, not a nontrivial solution. ABSTRACT, PAPER. |
| Regional Legendre/difference energy on a fixed nondegenerate interval | No as an extended source summand | Zero energy forces an almost-everywhere constant restriction. The analytic nonconstant \(g_0\) is not constant on an interval. It is not a stand-alone global minorant. ABSTRACT, PAPER. |
| Exterior endpoint gain of U1/COMPENSATE | No as an extended source summand | Its nonnegative weight is positive off its isolated minimum; its integral against \(|g_0|^2\) on an interval is positive. A lobe decomposition still requires its own exact source dictionary. ABSTRACT, PAPER. |
| \(w_m\|U_{\log m}f-f\|^2\) | No when \(\Lambda(m)>0\) | A nonzero periodic full-line L2 function is impossible, so the square is positive on \(g_0\). If \(\Lambda(m)=0\), the term is identically zero. ABSTRACT, PAPER. |
| The source square \(\|Af\|_{\mathscr H}^2/22\) | Yes, with exact kernel N | (K23), and nontriviality (K14); no RH. ABSTRACT, PAPER. |

For a nonnegative endpoint potential here, “extended source summand” means its literal positive integral on the relevant interval. The original regional/endpoint operators were not themselves defined as global operators on every theta test. No undeclared lobe parametrization of \(g_0\) is assumed.

### 5.5 All bounded positive forms with this vanishing property

Let P be a bounded positive sesquilinear form on \(\mathscr H\), represented by a positive B. If \(P[n]=0\) for all \(n\in\mathcal N_{\rm pt}\), Cauchy--Schwarz for P gives \(P(n,h)=0\) for every h. Equivalently,
\[
 Bn=0\ (n\in N),\qquad B=\Pi_{N^\perp}B\Pi_{N^\perp}. \tag{K34}
\]
Conversely this condition gives the vanishing. These are exactly the bounded positive forms on the Hilbert quotient \(\mathscr H/N\), pulled back to \(\mathscr H\). For a closed nonnegative form whose domain contains N, the same Cauchy--Schwarz argument descends it to the domain modulo N; the orthogonal representative gives the corresponding closed form on \(N^\perp\). Moreover any global positive minorant of Q on this completion is bounded by (K9), so the bounded classification covers the requested usable minorants. Equation (K1) supplies a nontrivial source-defined example with exact kernel; (K26) supplies another with different normalization. This proves the set is nonempty without RH. It does not assert that any such example is dominated by Q.

### 5.6 What the probe did and did not certify

The negative scalar decimals in [NP] and its positive HS decimals remain **FINITE_CELL / CONDITIONAL** diagnostics; no interval receipts or whole-tail bounds were rerun. The algebraic identity involving \(D_S+D_S^2\) remains exact on its stated trace domain. Equations (K29)--(K33) certify nonvanishing without ratifying those decimal values.

The source null test is noncompact, while the existing minus-class results are compact and restricted. The compact witness argument above is what licenses a *global* minorant refutation. A sign observed in the plus-channel and a claim that it has the same limiting mechanism are not proved by the null-family table. No whole-class scalar sign is inferred by subtracting close measured quantities.

## 6. Q3: consequence for the atom, and a usable discriminator for R

All algebra and transfer statements here are [ABSTRACT][PAPER]; the original all-support assertion remains [COFINAL_FAMILY][CONDITIONAL].

### 6.1 The premise of the proposed road exclusion is false

Q1(c)'s broad impossibility is false on the correctly specified reference space. It therefore cannot eliminate every source-square proof. What does survive is the necessary null-kernel test and the need for quantitative domination after that test passes.

The construction (K1) is not Connes' global trace formula, nor a proof of it. It is a bounded signed-form representation. Its remainder has the exact sign burden of the original problem, by (K11)--(K13). This is a coordinate change with an explicit kernel, not an analytical payment. The missing source inequality can be written as
\[
 \langle f,(A-A^2/22)f\rangle_{\mathscr H}\ge0
 \quad(f\in\mathscr H),                                \tag{K35}
\]
but the retained project name is still **ALL_SUPPORT_SIGNED_SCHUR_HEAD_LOWER_BOUND**, or the equivalent full same-direction comparison (A14). No new mandatory supplier is added.

Compactness plus agreement on a radical does not close (K35). On \(N\oplus\mathbb C^2\), the forms \(0_N\oplus I_2\) and \(0_N\oplus\operatorname{diag}(-1,1)\) have the same radical but opposite positivity behavior. Their nonzero parts are finite rank. An all-null-family identity cannot decide the remaining quotient sign.

### 6.2 Known partial results and route selection

**READ:** Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096v2, Theorems 1.1, 1.3, 1.4, and Section 2.3, (2.3)--(2.4). These give a Friedrichs realization, continuity of the lowest localized eigenvalue, a positive simple even minimum for sufficiently small support, and a regional energy identity. They are genuine non-square variational footholds; the small-support result is not an all-support comparison. The screw kernel's explicit formula, (1.3), does not carry its own positive-definiteness merely by being named a screw function.

Together with the returned COMPENSATE proof of its exact \(47/6000\) restricted tail, this favors a **signed head with a proved complement** over a search for another finite-S positive reservoir. The target is the sign of the complete coupled source operator, not a separate worst-case prime norm.

[READ, Connes 2026, Section 7] the characteristic-p/scaling-site program supplies geometric structures and correspondences, not the missing positive arithmetic intersection theorem. No number-field sign is imported from the finite-field analogy. [LM]'s Li/Bombieri--Lagarias summary remains a **relay here**, not a newly checked coefficient supplier. A coefficient criterion would still need a source proof of its coefficient signs and a crosswalk to (A14). None is supplied by this batch.

A Rayleigh maximum principle is not available merely because the reference energy is Dirichlet. The full source has the signed arithmetic and pole terms and a constrained test class; a positivity-preserving-semigroup or comparison theorem must be proved for that exact realization. No such new theorem is claimed.

### 6.3 The cheapest mathematical test of a proposed remainder

For the new Riesz square the exact dual formula is
\[
 \|Af\|_{\mathscr H}^2
 =\sup_{h\in\mathscr H}
       \{2\Re Q(h,f)-\|h\|_{\mathscr H}^2\}.            \tag{K36}
\]
It follows by completing the square in h. For a finite independent test list \(e_i\), let \(G^E_{ij}=\langle e_i,e_j\rangle_{\mathscr H}\), \(q_i=Q(e_i,f)\). Then
\[
 q^*(G^E)^{-1}q\le\|Af\|_{\mathscr H}^2,
 \quad
 R[f]\le Q[f]-\tfrac1{22}q^*(G^E)^{-1}q.                \tag{K37}
\]
The Gram is for a **proved positive reference metric**, not a Weil Gram. This is an **upper**, not lower, remainder test. A truncated dual maximum cannot certify \(R\ge0\).

For a genuine lower certificate, approximate Af by y and prove a full dual residual bound
\[
 \sup_{\|h\|_{\mathscr H}=1}
 |Q(h,f)-\langle h,y\rangle_{\mathscr H}|\le\epsilon.
                                                               \tag{K38}
\]
Then
\[
 Q[f]-\frac{(\|y\|+\epsilon)^2}{22}
 \le R[f]\le
 Q[f]-\frac{\max(0,\|y\|-\epsilon)^2}{22}.               \tag{K39}
\]
With interval source inputs, replace each side by the correctly directed outer endpoints. Every omitted reference-space direction belongs in (K38). Do not implement (K39) as subtraction of independently rounded close totals: assemble the combined source pairing \(Q(f,f-Af/22)\), or a completed mixed expression, before enclosures. The equations specify logical envelopes, not a license to violate rule 18.

For the fixed-width classes, (K36)--(K39) need the physical synthesis and the weighted reference Gram, including overlap. The proposition that every newly defined source form can already be evaluated in seconds is not established for this nonlocal reference solve. Nor would a finite positive R packet prove the infinite-class sign.

**Discriminator:** an exact strict upper value in (K37), or a rigorous upper envelope in (K39), below zero refutes the proposed remainder bound; a nonnegative lower envelope certifies only its declared domain. For this calibration, (K11) turns \(R[f]<0\) into \(Q[B^{1/2}f]<0\), with compact witnesses then obtained by the core argument. For an arbitrarily rescaled square that conclusion would be invalid. A straddling result remains inconclusive. The null family is useful for rejecting wrong kernels, but it cannot distinguish the positive quotient from an indefinite quotient sharing that kernel.

### 6.4 Two candidate representations, without authorizing a run

| Representation | Decisive object | Kill power / cost, ordinal | Status |
|---|---|---|---|
| Source Riesz square in (K7) | Kernel (K23), calibrated remainder (K35), full dual residual (K38) | 9/10 / 3/10 for paper audit; numerical cost unmeasured | Selected for this object question; not a new global-sign mechanism. |
| Direct physical-energy relative head | Original (A14) or full signed Schur complement, with all mixed terms and proved tail | 10/10 / 7/10 | Preferred subsequent sign research; no all-n payment supplied. |
| Adelic cutoff-trace realization | Exact number-field version of the global cutoff asymptotic and its comparison to the test form | 9/10 / 10/10 | Not selected; no presumed all-places positive projector. |

The estimates rank proposed investigations, not the probability that RH is true. No large computation, square-root-of-Weil construction, gauge scan, or packet enlargement is authorized here.

## 7. Strongest attack and exact scope of the findings

**Strongest attack on this verdict:** “You used Q itself to define A, squared it, and moved the unknown sign into R.” Correct. That is why the result is an answer to *existence and kernel*, not a proof-progress claim about the original sign. The explicit bound, exact radical proof and topology obstruction make the answer noncircular; they do not pay R. Rebranding it as a new RH proof mechanism would contradict (K11).

**Strongest attack on the request's impossibility:** it conflates existence of a positive detector with domination by the target form. (K1), (K14), and (K23) give a source-defined nonzero counterexample to emptiness of detectors. (K5) shows that even the correct kernel does not calibrate domination. Neither counterexample gives a negative Weil test.

| Refuted exact claim | Evidence | Kill scope / epistemics | Tags |
|---|---|---|---|
| No unconditional source positive form can have exact kernel N | (K6)--(K10), (K14), (K23) | THEOREM_SHAPE; COUNTEREXAMPLE; MATHEMATICALLY_DEAD on the declared completion | ABSTRACT/PAPER |
| Every correct-kernel fixed square automatically has an RH-equivalent remainder | (K5); normalization is independent of the kernel | THEOREM_SHAPE; COUNTEREXAMPLE to the general inference | ABSTRACT/PAPER |
| Fixed finite-S Sonin square globally minorizes Q on compact pole-null tests | (K30), strict upper witness below \(-a_S/2\) | THEOREM_SHAPE; COUNTEREXAMPLE; MATHEMATICALLY_DEAD for each fixed S | COFINAL_FAMILY/PAPER |
| Ordinary global L2 admits a nontrivial closable detector annihilating all null translates | (K24)--(K25) | THEOREM_SHAPE; FORMAL_IMPOSSIBILITY under the stated domain inclusion | ABSTRACT/PAPER |
| Pointwise vanishing always entails analytic divisibility with multiplicity | (K3), the \(z^2,z\) control; conditional multiple-zero version (K20) | THEOREM_SHAPE; algebraic inference refuted, no simplicity assertion for zeta | ABSTRACT/PAPER |

All witnesses and proofs are pinned by this new artifact and its source locks. No ROUTE_FAMILY kill is made. The quoted “same phenomenon” interpretation of the plus-channel has status UNRESOLVED, not a refutation or confirmation.

## 8. Predictions, handoff and closeout

### 8.1 Frozen observer predictions, with no event replacement

The original registrations are preserved here before scoring:

```text
  P_KERNEL_X_EXISTS_UNCONDITIONALLY: 0.35 — Q1(a) exhibits a source-defined X with ker X = 𝒩 exactly, without RH, with a proved identity Q = ‖Xf‖² + R.
  P_SQUARE_IDENTITY_IS_RH: 0.70 — Q1(b)/(c): any square identity with kernel 𝒩 and R ≥ 0 is RH-equivalent as a statement (Connes' global trace formula or its analogue), so the SOS road is a coordinate change.
  P_CC20_SQUARE_POSITIVE_ON_NULL: 0.85 — Q2: the CC20 archimedean square does not vanish on 𝒩 (it is positive on g_k).
  P_NO_SOURCE_FORM_VANISHES_ON_NULL: 0.55 — Q2: the set of nontrivial source-defined positive forms vanishing on 𝒩 is empty without RH (or Прошка proves it must be built from ξ's zeros).
  P_DIRECT_ROUTE_NAMED: 0.50 — Q3: a non-square proof shape for (A14) with at least one known partial result and locator is named.
```

| Prediction | p | Fate in this verdict |
|---|---:|---|
| P_KERNEL_X_EXISTS_UNCONDITIONALLY: source X, exact N kernel, unconditional signed identity | 0.35 | CONFIRMED_ON_EXPLICIT_ENERGY_COMPLETION by (K1), (K23). Not an ordinary-L2 assertion. |
| P_SQUARE_IDENTITY_IS_RH: any correct-kernel square with nonnegative remainder is RH-equivalent | 0.70 | PARTIAL: sufficiency is proved; equivalence is proved for existence and for our calibrated X. The general fixed-X converse is refuted by (K5), not by a claim about RH's truth value. |
| P_CC20_SQUARE_POSITIVE_ON_NULL: CC20 square does not vanish on N | 0.85 | CONFIRMED_NONVANISHING by (K27)--(K30). A finite positive decimal for the noncompact test is not interval-ratified. |
| P_NO_SOURCE_FORM_VANISHES_ON_NULL: nontrivial source positive forms annihilating N are absent without RH | 0.55 | REFUTED by the bounded source square \(A^2/22\). |
| P_DIRECT_ROUTE_NAMED: non-square route for (A14), with a known partial result and locator | 0.50 | CONFIRMED_AS_RESEARCH_ROUTE: signed variational head/complement, Suzuki Theorems 1.1/1.3/1.4 and (2.3)--(2.4); not an all-support proof. |

The second event is therefore not given an unqualified CONFIRMED. Its existential reading is correct. Its inference from kernel equality for an arbitrarily normalized fixed X is not. The toy control refutes that general inference; it does not decide the truth of a new equivalence for the actual zeta function. No numerical probability is edited.

### 8.2 Own ALIGN registrations scored against the returned independent audit

| Registration | Original p | Fate |
|---|---:|---|
| P_ALIGN_COVERAGE_SURVIVES_INDEPENDENT_REVIEW | 0.92 | CONFIRMED by [AC]. Its first coverage equivalence was independently re-derived. The separate CC20 citation debt is resolved by the direct reading in Section 4.2. |
| P_ALIGN_NEAR_NULL_AND_UNBOUNDED_PRIME_SURVIVE | 0.85 | CONFIRMED_AS_PAPER_AUDIT_OUTCOME. [AC] accepts the theta normalization, signed formula and growth argument; its numerical channels are diagnostics, not a universal proof. |
| P_ALIGN_DOMAIN_COMPLETION_SURVIVES | 0.90 | CONFIRMED_WITH_STATED_IMPORT: [AC] retains the finite-generator independence from the earlier check. Section 2.2 gives an explicit global reference-space core argument here; it is not represented as a rerun of that audit. |

The checker could not open CC20 Appendix C. This was a source-access limitation, not evidence that the pole-null criterion is false. The read text at (155) directly supports the imported implication. No old probability or artifact is changed.

### 8.3 New prospective registrations

These predict a future independent paper audit, not a result already observed:

- **P_KERNEL_RIESZ_RADICAL_AUDIT_SURVIVES**, p=0.85: the bound (K9), exact pointwise kernel (K23), and calibrated sign equivalence survive without a new RH premise or replacement of the stated completion.
- **P_KERNEL_L2_TOPOLOGY_OBSTRUCTION_SURVIVES**, p=0.96: an independent reviewer accepts (K25), including the density and graph-closure argument.
- **P_KERNEL_FIXED_S_RANK_ONE_FALSIFIER_SURVIVES**, p=0.91: the fixed-S compact witness (K30) and the nonzero-overlap proof for D2 survive with the stated cutoff and dilation conventions.

No new event is claimed to have preceded the derivations in this document. These are prospective audit predictions only.

### 8.4 One next directive — independent paper audit, not a numerical run

**KERNEL_REFERENCE_METRIC_RADICAL_AND_MINORANT_AUDIT.** Reconstruct (K6)--(K10) from the pinned geometric source, including the positive reference norm and the exact constant 65/3. Verify compact pole-null core density, the signed zero-series extension, the integral division (K19)--(K22), and the proof that all distinct zeros are separated without assuming simplicity. Attack the ordinary-L2 closure in (K25) independently. Re-derive the physical dilation coefficients in (K32), then test the rank-one compact falsifier before accepting a global reservoir statement.

Success means the same source-defined bounded X on (K7), exact kernel (K2), equivalence (K13) with sign still unproved, and the strict upper witness (K30). First-failure code: **KERNEL_REFERENCE_DOMAIN_OR_RADICAL_IDENTIFICATION_GAP**; a failure must name the earliest unsupported identity and its weakest repair. Do not rerun probe grids, enlarge a packet, take \(S_n^{1/2}\), edit Lean, submit Aristotle, or promote state. This is the cheapest decisive check because it can invalidate the new object answer without any source-matrix computation.

### 8.5 Consumer contract and memory

**DOWNSTREAM_CONSUMER:** unchanged published Weil criterion on compact complex tests, with the verified sufficient pole-null ideal. **ACTUAL_CONSUMER_REQUIREMENT:** full source nonnegativity, or the accepted vanishing-negative-error interface on exhausting supports. **ORIGINAL_REQUESTED_OBJECT:** source square with exact null kernel and an identified remainder. **ORIGINAL_OBJECT_IS:** NOT_NECESSARY as a particular proof method; only (K4) is necessary for a fixed positive decomposition extending to N. Exact kernel equality and the chosen reference metric are not compulsory for every admissible proof.

**KNOWN_WEAKER_INTERFACES:** direct (A14), a signed head with complete complement, or vanishing all-support lower errors. Our calibrated (K35) is equivalent, not claimed weaker. **FAILURE_TYPE / EPISTEMIC_STATUS:** NO_DERIVATION / RESEARCH_DEBT for the all-support sign. **REOPEN_TRIGGER:** a source proof of the directional inequality on the quotient, an all-n full-residual lower certificate, or a strict negative upper source witness. **NOVELTY_AXIS:** domain-sensitive kernel construction and separation of kernel correctness from sign; no historical priority claim.

**What became smaller:** the claimed need to discover a source operator with the right kernel is discharged on an explicit completion. The remaining sign cannot be blamed on nonexistence of source quotient data. **What was killed:** the broad source-detector impossibility and the fixed-S global reservoir theorem shape, not the all-prime route. **Must not recur:** use ordinary L2 closure as if zero evaluations were continuous; equate pointwise zeros with multiplicity divisibility; treat nonzero squares as paid lower bounds; infer a global limit mechanism from one drifting finite probe.

**Smallest retained gap:** ALL_SUPPORT_SIGNED_SCHUR_HEAD_LOWER_BOUND / exact same-direction source domination. **Progress class:** REPRESENTATION_PROGRESS plus FALSIFICATION_PROGRESS, no analytic RH-supplier closure. **Cognitive operator:** REPRESENTATION_SHIFT. **Route score:** 3, useful object resolution but nondecisive for the universal sign. **Memory:** a correct null kernel can be built unconditionally; a calibrated source square preserves the unresolved quotient inertia. The next check must test that kernel and topology, not celebrate the square as a proof.

### 8.6 Publication and verification handoff

Only `EXPECTED_VERDICT_PATH` is written on `rh_clean`; the commit subject begins `[Proshka]`. The delivery receipt records its commit, parent, exact blob, SHA-256, line count, final LF and one-file diff. Those receipts validate delivery, not the mathematics. All new proofs are PAPER, pending the audit above. No Lean source was written, no kernel build was run, and no axiom profile is claimed; Lean working-directory gate commands are therefore not applicable to this documentation-only transaction.

## Appendix A. Exact ledger and boundary checks

All statements in this appendix are [ABSTRACT][PAPER]. These are analytical or rational checks, not numerical experiments.

1. For t positive, \(A_0(t)\le1+1/(2t)\); near zero \(A_0(t)=1/(2t)+O(1)\), and at infinity it decreases exponentially. Thus \(\int A_0\min(4,C^2t^2)<\infty\), as required in the core argument. The displayed upper bound follows from \(1/(1-e^{-2t})\le1+1/(2t)\).
2. The decreasing function \(\log x/x^{3/2}\) on \([2,\infty)\) has sum at integers bounded by its value at 2 plus its integral from 2. Their sum is below \(2\log2+4<6\). The weaker last bound suffices; \(\Lambda(m)\le\log m\) includes every prime power.
3. \(c_A<7\) follows from \(\gamma_E<1\), \(\pi<4\), and \(\log(8\pi)<4\). Hence the absolute weighted-L2 coefficient is \(7+12+8/3=65/3<22\).
4. The pole dual integrals are exactly \(\int e^{x-2|x|}dx=1+1/3=4/3\) and its reflected counterpart. This fixes both rank-two pole coefficients and the bound (K8).
5. For (K14), \(2A_0(t)\ge e^{-1/2}/t\) on \(0<t\le1\). Since \(e^{-1/2}>1/2\), \(\log2>2/3\), and \(\log(1/d)=24\log2\), \(2\int_d^1A_0(t)dt>8\). The support length d is below \(\log2\), so all prime autocorrelations vanish. Subtracting \(c_A<7\) gives a strict floor greater than one. Nonzero compact \(\eta\) cannot solve \(\eta''=\eta/4\) globally, so the pole-null f is nonzero.
6. The reference perturbation bounds are exact: \((65/3)/22=65/66\); hence \(I-A/22\) lies between \(I/66\) and \(131I/66\). No target sign is used in obtaining its square root.
7. For (K19), on either tail the relevant integral is bounded by \(\int_{|x|}^\infty e^{Ct-c e^{2t}}dt\). Absorbing the exponential prefactor into half of the double exponential gives \(C'\exp(-c'e^{2|x|})\). Differentiating the first-order equation repeatedly gives the same type of estimate for all derivatives. This pays every boundary integration-by-parts term in (K20)--(K22).
8. Repeated integration by parts against \(e^{(\sigma+iT)x}\), with \(|\sigma|\le1/2\), bounds compact approximants of (K21) by \(C_N(1+|T|)^{-N}\), uniformly in cutoff. The cutoff derivatives and the tail terms are bounded by item 7. Taking N greater than three and using the unconditional zero count makes (K16) absolutely and uniformly summable. Multiplicity is included in that count.
9. In the compact minorant falsifier, the two strict thresholds are \(a_S/4\) and \(3a_S/4\); the combined upper bound is \(-a_S/2\). Their existence is proved by norm convergence, not chosen from a fitted floor. This is a symbolic eventual witness, not a claim of a computed entrance radius.
10. A nonzero translation-invariant periodic L2 function cannot exist: integrating its squared modulus over disjoint periods would diverge. Fourier uniqueness in (K25) is applied to an L1 product, by Cauchy--Schwarz, not to an unjustified distributional point value.

## Appendix B. First-source inventory and unclaimed imports

- **READ:** Connes 1999, arXiv:math/9811068v1, Section III Theorem 1 and Corollary 2, pp.13--15; Section VIII (16), Theorem 5, pp.41--42; number-field cutoff discussion (33), pp.46--47. PDF theorem pages visually inspected. No source-only positive all-zero minorant imported.
- **READ:** CC20, arXiv:2006.13771v1, Introduction (1)--(5), Theorem 1; Section 6.7 Theorem 11; Appendix B explicit-formula conventions; Appendix C Proposition 1 (155). The last locator closes the returned checker's missing-source issue. No support extension imported.
- **READ:** CCM23, arXiv:2310.18423v2, Definition 2.2, Theorem 3.1, Definition 4.5, (57)--(59), Theorem 4.6, Section 4.8. Finite-S spaces and transport, not exact global-zero spectrum.
- **READ:** Connes 2026, arXiv:2602.04022v1, Sections 6.4--6.6, (20)--(21), Fact 6.4; Section 7. Null-range and approximation discussion, not positivity supply.
- **READ:** Suzuki, arXiv:2606.09096v2, Theorems 1.1, 1.3, 1.4; (1.3), (2.3)--(2.4). Local variational partial results only.
- **READ_STATEMENTS_ONLY, NOT_USED_AS_SUPPLIER:** Zhu, arXiv:2608.24827v2, Theorems 1.1--1.2 and Section 6's normalization qualification. No numerical certificate independently checked, no CCM normalization transfer asserted here.
- **RELAY_ONLY:** the literature map's universal-history claims, Li/Bombieri--Lagarias coefficient discussion and de Branges route-wide conclusions. No theorem from them is an input to (K1)--(K39).

## 9. PROSHKA'S OWN LINE

I choose the source Riesz representation because this batch asks whether the right kernel can exist before the sign is known.
It can, once the reference topology is made explicit.
That answer should prevent another search for an object whose elementary existence was mistaken for the main obstacle.
The first nearby alternative was to project onto the zero ideal in ordinary L2.
The null translates are dense there, so that proposal has no nontrivial closable detector.
The second was to import an all-places Sonin square from the spectral-realization literature.
The papers distinguish their unconditional cokernels and finite transports from the missing positive global comparison.
I keep that distinction rather than promote an evocative name into an operator theorem.
The source operator constructed here contains the full signed arithmetic form.
Squaring it preserves its kernel and deliberately removes its sign.
The calibrated remainder puts exactly that unresolved sign back.
That is useful for the object question but is not a shortcut to the terminal theorem.
The first move beyond this batch is an independent audit of the weighted core and the exact radical proof.
A failed strip bound, an omitted multiplicity, or a nonuniform zero-series passage would invalidate that identification.
The second move is to return to the signed physical head with its complete complement.
A rigorous negative upper source witness would decide against the proposed sign.
A negative sufficient lower bound would only reject that particular payment.
I would ask for a combined source pairing and a full reference-space residual before a new numerical remainder table.
I would also ask that every proposed square declare its domain and the topology of its kernel.
The positive Sonin values on the null family were the useful surprise in the probe.
Their significance is structural, not the number of displayed digits.
An injective convolution multiplier cannot erase a nonzero fixed reservoir.
A single reservoir vector is enough to turn that observation into a strict compact-test falsifier.
I distrust the leap from those values to every support-dependent finite-prime construction.
I also distrust the identification of the drifting plus-channel sign with a proved limiting mechanism.
The full null family and a finite local packet do not have the same domain.
The kernel of a quadratic representation and the size of that representation are independent data.
A correct-kernel square can still be much too large for the Weil form to pay.
The next useful theorem must control that payment on the quotient, not merely recognize its null vectors.
No all-support sign is claimed by this verdict.
