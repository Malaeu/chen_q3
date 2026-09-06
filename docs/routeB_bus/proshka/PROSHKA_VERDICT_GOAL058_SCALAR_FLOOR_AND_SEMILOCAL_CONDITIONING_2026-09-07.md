# STATUS: TRY_SCALAR_FLOOR_SQUARE_IDENTITY_AND_EULER_GRAM_CERTIFICATION
```yaml
OPERATIVE_CLASS: TRY_SCALAR_FLOOR_SQUARE_IDENTITY_AND_EULER_GRAM_CERTIFICATION
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-07-SCALARFLOOR
BOUNDARY_ID: GOAL058_SCALAR_FLOOR_LEMMA_AND_SEMILOCAL_CONDITIONING
RESULT:
  Q1: PARTIAL_WITH_PRECISE_REMAINDER
  Q1a: PROVED_ON_CLASS
  Q1b: PARTIAL_WITH_PRECISE_REMAINDER
  Q1c: PROVED_ON_CLASS
  Q2: PARTIAL_WITH_PRECISE_REMAINDER
  Q2a: PARTIAL_WITH_PRECISE_REMAINDER
  Q2b: PROVED_ON_CLASS
  Q2c: PARTIAL_WITH_PRECISE_REMAINDER
  Q3: PARTIAL_WITH_PRECISE_REMAINDER
  Q4: COMPUTATION_SPECIFIED
REQUEST_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  COMMIT: 9a61c748c465c94cda3f35d754bd00b08cb75e36
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_SCALAR_FLOOR_AND_SEMILOCAL_CONDITIONING_2026-09-07.txt
  GIT_BLOB: fbfc4ce550a5716a77415b589cfd33d4631a919b
  SHA256: 727572551491e9a4374172c24ba1c2b7d16224f8f0263bc0bcd97a5ac5d3cbc7
  BYTES: 14243
  LINES: 111
  FINAL_LF: true
  GITHUB_CONNECTOR_FETCH: true
  FETCHED_UTF8_REENCODING_SHA256_AND_GIT_BLOB_RECOMPUTED: true
  ALL_FOUR_CHECKS_MATCH: true
BOOTSTRAP:
  REF: rh_clean
  PATH: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
  GIT_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_SECOND_EXPRESSION
  SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
  TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false
CLOSES: [REQ-2026-09-07-SCALARFLOOR]
CLOSES_ANALYTIC_RH_SUPPLIERS: []
CLOSED_REVIEW_OBLIGATIONS:
  - SCALARFLOOR_EXACT_D_PLUS_D_SQUARED_PROJECTION_IDENTITY
  - SCALARFLOOR_POSITIVE_PACKET_REMAINDER_AND_SCALAR_BRACKETS
  - SCALARFLOOR_BSTAR_SIGNED_ANGLE_GAP_TRANSFER
  - SCALARFLOOR_EULER_GRAM_DENSITY_RESIDUAL_CERTIFICATE
  - SCALARFLOOR_EXPLICIT_UNIFORM_MELLIN_J_TAIL_MAJORANT
  - SCALARFLOOR_FALSE_FACTOR_INFIMUM_SHIFT
OPENS: []
CLOSES_ARE_REVIEW_RESULTS_NOT_NEW_LEAN_CATALOG_EXPORTS: true
DECISIONS:
  TRUE_OPERATOR_FLOOR_LEMMA: PAPER_PROVED
  POSITIVE_REMAINDER: squared_Hilbert_Schmidt_norm_of_test_times_D
  SCALAR_FLOOR_NONNEGATIVE_ON_WHOLE_R1_MINUS_CLASS: not_proved
  SCALAR_FLOOR_NONNEGATIVE_ON_EXPLICIT_INFINITE_DIMENSIONAL_SUBCLASS: not_proved
  ACTUAL_R1_MINUS_REFUTED: false
  FROZEN_TEST_OR_H4_INTERVAL_POSITIVITY_CERTIFICATE: absent
  H4_MARGIN_0_0035_IS_A_PROVED_LOWER_BOUND: false
  EXACT_FIXED_CUTOFF_ANGLES_CONVERGE_TO_PLUS_OR_MINUS_ONE: false
  TWO_NEAR_UNIT_SOURCE_ANGLES_CERTIFIED: false
  ONE_NEAR_UNIT_ANGLE_PER_ADDED_PRIME: not_established
  STABLE_SOURCE_REPRESENTATION_WITHOUT_SEMILOCAL_ANGLE_DENOMINATOR: true
  STABILITY_UNIFORM_IN_GROWING_S: false
  TRUE_K2_NONNEGATIVE: true
  TRUE_D2_SIGN_ON_ALL_OF_5_TO_16: unresolved
  TRUE_D2_AT_2PI_OVER_LOG2: strictly_positive_paper_bound
  LOW_FREQUENCY_MASS_IS_EXACTLY_IRRELEVANT: false
  DROPPING_SPURIOUS_APPROXIMATE_MODES_IS_A_SOURCE_LOWER_CERTIFICATE: false
  SETTING_UNSPECIFIED_TAIL_CONSTANT_TO_ONE_IS_A_CERTIFICATE: false
  PLANTED_INFIMUM_EQUALS_TRUE_INFIMUM_MINUS_DELTA_M: true
  BOTH_INFIMA_EQUAL_ZERO: false
REMAINS_OPEN:
  - SEMITABLE_R1_MINUS_AT_FIXED_CUTOFF_1
  - NONNEGATIVITY_OF_THE_EXPLICIT_SCALAR_FLOOR_ON_THE_POLE_NULL_CLASS
  - CERTIFIED_SINGLE_TEST_SCALAR_FLOOR_WITH_FULL_ERROR_BUDGET
  - CERTIFIED_TEST_SPECIFIC_FALSE_FACTOR_SURVIVAL_OR_DETECTION
EVIDENCE_BOUNDARY:
  CUTOFF: 9a61c748c465c94cda3f35d754bd00b08cb75e36
  ANOTHER_SCALARFLOOR_JUDGE_VERDICT_USED: false
  POST_REQUEST_ANALYTIC_RESULTS_USED: false
  OBSERVER_VALUES: DIAGNOSTIC_NOT_INTERVAL_CERTIFICATES
  ALL_SHELF_SHA256_PREFIXES_RECOMPUTED: false
NEW_RESULTS:
  SCOPE: ABSTRACT
  VERIFIER: PAPER
  INDEPENDENT_REVIEW: pending
  LEAN_KERNEL_VERIFIED: false
  HISTORICAL_NOVELTY: not_claimed
EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SCALAR_FLOOR_AND_SEMILOCAL_CONDITIONING_2026-09-07.md
AUTHORIZED_WRITE_SCOPE: VERDICT_DOC_ONLY
HASH_COMPUTATION_PERFORMED: true
NUMERICAL_RUN_PERFORMED: false
SYMBOLIC_SOFTWARE_EXPERIMENT_PERFORMED: false
LEAN_EDIT_PERFORMED: false
ARISTOTLE_SUBMISSION: false
QUEUE_OR_SHARED_STATE_EDIT: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## 0. Decision and evidence boundary

**The floor lemma is true. The quoted positive numerical floors are not yet certificates.** There is a stronger exact identity: the difference between the true margin and the scalar floor is a squared Hilbert--Schmidt norm. There is also a source-specific change of representation which removes the *semilocal* near-unit-angle denominator. Neither result establishes the scalar sign on the whole phase class. [ABSTRACT][PAPER]

Two statements in the request require explicit rejection, not silent reconciliation. At fixed cutoff the true compact compression has norm strictly below one; a discretization parameter does not make its eigenvalues converge to exactly ±1. Also, the false factor shifts every normalized margin by the same negative constant, so the two class infima cannot both be zero. The reported single-test plant outcomes remain unverified because their required upper/lower source envelopes have not been supplied.

### Sources actually read

All repository paths below are at the request commit unless stated otherwise.

**[R]** `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_RESERVOIR_RESONANCE_AND_PRIME_SCALING_2026-09-06.md`: source definitions, (2)--(18), exact periodization, high-modulation family, (36), and predictions. Its derivations are rechecked, not imported as axioms. **[RI]** `docs/routeB_bus/RESONANCE_INDEPENDENT_CHECK_2026-09-06.md` reports eleven algebraic/analytic checks, but expressly separates numerical corroboration from analytic justification.

**[PP2]** `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_PHASE_CLASS_INEQUALITY_AND_MOLLIFIER_CROSSWALK_2026-09-06_UPLOADED_VERSION.md`, blob `9884019c5ed76f67225c9777a1cd91f115707ef5`: full-residual Galerkin sandwich and the exact frozen event `P_PHASEPROOF_SOURCE_PACKET_MINUS_MARGIN_POSITIVE`. The first PHASEPROOF version is a distinct artifact; neither version is overwritten.

**[DR]** `docs/routeB_bus/D2_SOURCE_EXACT_EVALUATOR_REPORT_2026-09-06.md`, blob `efc7ed450e7dc2c30cc350b47dbf3df3d1c7a749`. **[DP]** `docs/routeB_bus/phase5_codex/mellin_d2/PROGRESS.md`, blob `c717a1de9a3ad8fb751ce44b3738985da4564a7d`.

**[OP]** `docs/routeB_bus/phase5_codex/mellin_d2/prod_op.py`, blob `dd7b88003c2a087419248205a2f5f531c239191b`, explicitly uses `keep = abs(lam) < 1.0 - 1e-12`. **[TS]** `docs/routeB_bus/phase5_codex/mellin_d2/prod_t.py`, blob `1e58c9cb99fcc9fd67def4bad6a46f75a4e04d19`, explicitly sets the unspecified tail-shape constant to one. Both scripts were read, not executed. These two code facts materially change the certification verdict.

**[CC20]** Connes--Consani, arXiv:2006.13771v1, Theorem 4.7, (83)--(84), Appendix D: tested Sonin/angle traces. **[CCM23]** Connes--Consani--Moscovici, arXiv:2310.18423v2, Proposition 4.6, (57)--(59), Theorem 4.6: finite Euler intertwining and the bounded invertible Sonin-space map. The relevant CCM23 PDF formulas were visually checked. The CC20 text was read; the PDF screenshot service failed for its requested page. **[DLMF]** NIST DLMF 5.7.6 and the psi-function special-value/functional relations are used only for the explicit low-frequency sign check in §5.3. No new result from arXiv:2602.04022v1 or math/9811068v1 is needed beyond the source convention already rederived in [R].

The request was fetched through GitHub. Its complete UTF-8 text was re-encoded locally, including the final LF; SHA-256, Git blob SHA-1, bytes and lines all matched. Other shelf SHA-256 prefixes are not all recomputed. No table value is a premise in a proof below.

## 1. Objects, normalization, and what has to have a sign

Write
\[
 a=\log2,\quad r=2^{-1/2},\quad
 \delta=\frac{\log3-\log2}{8},\quad I=(-\delta,\delta),
\]
\[
 \mathcal H_{00}(I)=\{h\in C_c^\infty(I;\mathbb C):
       \int h(x)e^{x/2}dx=\int h(x)e^{-x/2}dx=0\}.
\]
Use \(U_ch(x)=h(x-c)\), \(T_hg=h*g\), and the nonunitary transform
\(\widehat h(\xi)=\int h(x)e^{-i\xi x}dx\). Inner products are antilinear in the first slot. For nonzero \(h\), put
\[
 H=\|h\|_2^2,\qquad
 v_h=\frac{U_{a/2}h-U_{-a/2}h}{\sqrt{2H}},\qquad
 W_h(\xi)=\frac{(1-\cos(a\xi))|\widehat h(\xi)|^2}{H}.
 \tag{1}
\]
The lobes are disjoint, \(\|v_h\|=1\), and their diameter is less than \(\log3\). The pole terms vanish and the prime-2 contribution is already included in \(L_2\). In particular,
\[
 \int W_h=2\pi,\qquad
 \mathfrak m(h)=L_2(v_h)-n_2(v_h)=-\int W_h(\xi)d_2(\xi)d\xi.
 \tag{2}
\]
The first equality follows from Plancherel and the vanishing autocorrelation of \(h\) at \(a\). One must not add the atom \(w\) again to the last expression. [ABSTRACT][PAPER; conventions R]

For fixed finite \(S\), let \(P\) be the physical cutoff on \((0,1)\), \(F_S\) the exact real Fourier involution, \(Q_S=F_SPF_S\), and \(\mathsf S_S\) the orthogonal projection onto \(\ker P\cap\ker Q_S\). Define
\[
 D_S=P+Q_S-I+\mathsf S_S,\quad
 A_S=E^*F_SE,\quad \alpha_S=\|A_S\|<1,
 \quad Z_S=(I-A_S^2)^{-1}.
\]
Here \(E\) is zero extension from \((0,1)\). Keep \(P\) distinct from the archimedean Sonin projection \(P_0=\mathsf S_\infty\), used later.

The continuous source densities and scalar are
\[
 k_S=\frac{q_S}{2\pi}+d_S,\quad
 \ell_S(\xi)=2\Re(\gamma_S(\xi)t_S(\xi)),\quad |\gamma_S|=1,
\]
\[
 \mathcal F(h):=-\int W_h\ell_2.
 \tag{3}
\]
The notation \(\mathcal F(h)\) in this document means the requested scalar floor, not the unitary Fourier operator, which is written \(\mathscr F\). The target \(\mathcal F(h)\ge0\) remains a separate assertion.

## 2. Q1(a): a source operator proof of the floor

### Theorem 1. Exact square remainder

For any two orthogonal projections \(P,Q\), with \(S_0\) the projection onto their common kernel and \(D=P+Q-I+S_0\),
\[
 \boxed{D+D^2=PQ+QP.}                                      \tag{4}
\]
For the source operators, after insertion of a smooth compact test \(v\),
\[
 \boxed{
 L_S(v)-n_S(v)
 =-\operatorname{Tr}\bigl(T_v(PQ_S+Q_SP)T_v^*\bigr)
       +\|T_vD_S\|_{HS}^2.}                              \tag{5}
\]
Consequently, on the phase class,
\[
 \boxed{\mathfrak m(h)=\mathcal F(h)+\|T_{v_h}D_2\|_{HS}^2
                 \ge\mathcal F(h).}                     \tag{6}
\]
All these claims have scope **ABSTRACT**, verifier **PAPER**.

**Proof.** Set \(K=P+Q\). Since \(KS_0=S_0K=0\),
\[
 D^2=K^2-2K+I-S_0,
 \quad D+D^2=K^2-K=PQ+QP.
\]
Thus the positive remainder is literally \(D^2\), not an assumed sign of a numerical eigenvalue sum. The tested trace formula gives
\(n_S(v)-L_S(v)=\operatorname{Tr}(T_vD_ST_v^*)\). Apply (4), and use
\(\operatorname{Tr}(T_vD_S^2T_v^*)=\|T_vD_S\|_{HS}^2\).

The trace statements are about smooth-test sandwiches. The smooth half-line commutator/Hankel argument in [R, Lemma 2] supplies their trace domains; the bare semilocal \(D_S\) is not asserted Hilbert--Schmidt. To identify the first trace with \(\int|\widehat v|^2\ell_S\), let \(W=(E,F_SE)\). Then
\[
 PQ_S+Q_SP=W\begin{pmatrix}0&A_S\\ A_S&0\end{pmatrix}W^*.
\]
On the generalized Mellin wave \(f_\xi(u)=(2\pi)^{-1/2}u^{-1/2+i\xi}\), its two coefficients are \(f_\xi|_{(0,1)}\) and \(\gamma_S(\xi)f_{-\xi}|_{(0,1)}\). The two cross terms give \(2\Re(\gamma_St_S)\). Evaluate after testing, or cut the Mellin integrals off first and use their locally convergent source formulas. This is the same source calculation as [R, (6)], now supported by the independent polynomial identity (4). Substitution of (1) proves (6). QED.

### Pointwise version and exact assumptions

There is also a direct proof avoiding any unproved expansion of the non-square-integrable Mellin wave. Write \(u=u_S(\xi)\in L^2(0,1)\), choose any phase \(\phi\) with \(\gamma_S=e^{i\phi}\), and set
\[
 X=\Re(e^{-i\phi/2}u),\qquad Y=\Im(e^{-i\phi/2}u).
\]
Reality and self-adjointness of \(A=A_S\), together with [R, (6)], give
\[
 \boxed{\ell_S-d_S
 =2\langle X,(I+A)^{-1}X\rangle
  +2\langle Y,(I-A)^{-1}Y\rangle\ge0.}                    \tag{7}
\]
Indeed \((I-A)Z=(I+A)^{-1}\) and \((I+A)Z=(I-A)^{-1}\); expansion into real and imaginary parts proves the formula. Changing the square-root phase changes both signs and not the value. The hypotheses needed for this argument are a real self-adjoint \(A\) with \(\|A\|<1\), a unimodular \(\gamma\), an actual \(L^2\) vector \(u\), and the source identity (6) of [R]. The global projection proof needs neither a real eigenbasis nor a formal untested trace. [ABSTRACT][PAPER]

In an eigenbasis, (7) recovers exactly the mode expression in the request. Absolute convergence of the correction follows from
\(\sum_n|u_n|^2<\infty\) and \(1-|\lambda_n|\ge1-\alpha_S\). One does **not** assume \(\sum|c_n|^2<\infty\); the uncut \(f_\xi\) is not in \(L^2(0,1)\). Nor is an absolutely convergent expansion \(t_S=\sum\lambda_n\bar c_n^2\) required by the proof. The separately defined Mellin integral supplies \(t_S\). Continuity of the source formulas upgrades the almost-everywhere density inequality to their continuous representatives at every real \(\xi\).

**Planted failure.** Put \(A=2\), \(c=i\), \(u=2i\), \(\gamma=1\), \(t=-2\) in the algebraic expression [R, (6)]. It gives \(d=4>\ell=-4\). Thus substituting a noncontraction into that expression does not preserve the floor. This is an exact counterexample to that extension, not to the source theorem. [ABSTRACT][PAPER; THEOREM_SHAPE]

### Packet statement: retain the coefficient Gram

For a finite list \(h_j\), polarize the **unnormalized numerators**:
\[
 M_{ij}=-\int(1-\cos a\xi)\overline{\widehat h_i}\widehat h_j\,d_2\,d\xi,
 \quad F_{ij}=-\int(1-\cos a\xi)\overline{\widehat h_i}\widehat h_j\,\ell_2\,d\xi.
\]
Then
\[
 \boxed{\mathbf M-\mathbf F\succeq0.}                     \tag{8}
\]
For every complex coefficient vector, its quadratic value is the integral of a nonnegative density times the modulus square of the synthesized transform, or the corresponding norm square in (5). Normalized \(\mathfrak m(h)\) itself is a Rayleigh quotient, not a quadratic form. Its denominator is the packet Gram \(H(c)=\|\sum c_jh_j\|^2\); normalized row values alone are not the matrix (8). [FINITE_CELL][PAPER]

## 3. Q1(b)--(c): what the scalar sign needs; matching scalar brackets

### 3.1 The sign has not followed from the peak alignment

The exact remaining sufficient inequality is
\[
 \boxed{-\int_{\mathbb R}(1-\cos a\xi)|\widehat h(\xi)|^2
           \ell_2(\xi)d\xi\ge0,
                 \qquad h\in\mathcal H_{00}(I).}          \tag{9}
\]
It has zero budget and an explicitly fixed scalar multiplier. No universal sign or independently specified infinite-dimensional positive subclass is proved here. No admissible \(h\) with a certified negative value of (9) is supplied either. Failure to prove (9) does not refute \(\mathfrak m\ge0\), because (6) has a nonnegative remainder.

Two concrete attempted shortcuts fail. First, \(|t_2|\) does not determine \(\Re(\gamma_2t_2)\). Second, the periodic phase marginal constrains only periodic multipliers. For every integrable periodic \(b\), support shorter than \(a\) gives
\[
 \frac1H\int|\widehat h(\xi)|^2 b(a\xi)d\xi
       =\int_0^{2\pi}b(\theta)d\theta.                    \tag{10}
\]
To prove this, periodize \(|\widehat h|^2\); its nonconstant Fourier coefficients are the zero autocorrelations at nonzero multiples of \(a\), and its constant value is \(aH\). The multiplier \(\ell_2\) is not periodic: it tends to zero at infinity by the source Mellin estimates. A literal, fixed-height Poisson-kernel description of \(|t_2|\) cannot hold globally. A finite-frequency pattern, or a periodic modulation of a decaying envelope, is different. Neither supplies (9). [ABSTRACT][PAPER]

There is an exact obstruction to a proposed periodic scalar certificate. If a continuous periodic \(b(a\xi)\) satisfies \(b(a\xi)\le-\ell_2(\xi)\) on the whole real line, then fixing a phase and sending \(\xi\) to infinity along it gives \(b\le0\). Hence its weighted mean \(\int(1-\cos\theta)b(\theta)d\theta\) cannot be positive. This kills a **positive periodic pointwise minorant**, not the restricted scalar inequality. It explains why the exact phase theorem cannot supply a positive floor on its own. [ABSTRACT][PAPER; THEOREM_SHAPE]

### 3.2 A precise compact test-space representation

Let \(E_I\) be zero extension and \(P_{00}\) the projection in \(L^2(I)\) orthogonal to \(e^{x/2},e^{-x/2}\). With \(\mathscr F\) unitary, define
\[
 \mathcal T=-2\pi P_{00}E_I^*\mathscr F^{-1}
       M_{(1-\cos(a\xi))\ell_2(\xi)}\mathscr F E_IP_{00}.
 \tag{11}
\]
Then \(H\mathcal F(h)=\langle h,\mathcal Th\rangle\). This self-adjoint operator is compact: cut its bounded multiplier off at \(|\xi|\le X\), obtaining a square-integrable kernel on \(I\times I\); the omitted multiplier norm tends to zero. Smooth pole-null functions are dense in the closed moment-null subspace, by smooth approximation followed by correction with two fixed smooth functions having independent moment vectors. Therefore (9) is exactly positivity of this **source-defined compact operator**, not a finite list of diagonal tests. [ABSTRACT][PAPER]

This representation retains the support, both moments, all complex directions and the actual multiplier. A finite positive compression does not certify its infinite complement. Defining a subclass to be its unknown positive spectral subspace would rename the missing sign, not prove it. A frequency-gap subclass also does not work literally: a nonzero compactly supported smooth function has an entire transform and cannot have an open spectral gap.

### 3.3 Two scalar integrals bracket the margin

Equation (7) and the spectral bounds for \(I\pm A\) give
\[
 \frac{2}{1+\alpha_S}\|u_S(\xi)\|^2
 \le \ell_S(\xi)-d_S(\xi)
 \le \frac{2}{1-\alpha_S}\|u_S(\xi)\|^2.
 \tag{12}
\]
Thus, putting \(U(h)=\int W_h\|u_2\|^2\),
\[
 \boxed{\mathcal F(h)+\frac{2U(h)}{1+\alpha_2}
 \le\mathfrak m(h)\le
 \mathcal F(h)+\frac{2U(h)}{1-\alpha_2}.}                 \tag{13}
\]
In particular \(\mathfrak m(h)\ge\mathcal F(h)+U(h)\), without knowing a numerical angle gap. The upper bound needs a proved bound \(\alpha_2<1\); §4 supplies an archimedean transfer for it. These integrals use the explicit Mellin vector and its squared norm, not an inverse applied to each frequency. They still need scalar/vector quadrature and tail enclosures. [ABSTRACT][PAPER]

There is no uniform upper estimate for the correction from \(\|u\|\) alone over all contractions approaching one. In one dimension take \(A=1-\varepsilon\), \(\gamma=1\), \(u=i\). Equation (7) gives \(\ell-d=2/\varepsilon\) while \(\|u\|=1\). Rewriting a general resolvent as two shifted resolvents cannot eliminate that sensitivity. This does not rule out the source-specific representation below.

## 4. Q2(a)--(b): source conditioning, a quantitative transfer, and a stable representation

### 4.1 The alleged limits ±1 are not the fixed-cutoff source theorem

For one prime the exact Fourier involution is
\[
 F_p=\left((1-r_p^2)\sum_{j\ge0}r_p^jU_{-ja_p}
                            -r_pU_{a_p}\right)F_\infty.
\]
The series converges in operator norm; each cutoff-compressed term is compact. Finite products give compactness for fixed finite \(S\). The exact unimodular multiplier gives self-adjointness and unitarity. If the compact compression had an eigenvalue of modulus one, a nonzero cutoff-supported vector and its \(F_S\) transform would both be cutoff-supported. Applying \(B_S^*\), using
\[
 F_\infty B_S^*=B_S^*F_S,
 \quad B_S=\prod_{p\in S\setminus\{\infty\}}(I-r_pU_{a_p}),
 \tag{14}
\]
would give an ordinary compactly supported function with compactly supported cosine transform. Entire-function uniqueness forbids this. Hence \(\|A_S\|<1\). [ABSTRACT][PAPER; R, CCM23]

The operator error \((1+r)r^{J+1}\) belongs to approximation of this *fixed* operator. Provided quadrature also converges in the required operator sense, its eigenvalues converge to source eigenvalues strictly inside \((-1,1)\), not to ±1. Values outside this interval and an extrapolated limit above one cannot establish source limiting values. “Two near-unit angles” additionally needs a specified threshold and a certified count. Non-Hilbert--Schmidt behavior concerns infinitely many small angles approaching zero; it does not count a near-unit cluster.

### Theorem 2. Euler transport bounds both signed angle gaps

Set
\[
 b_-:=\prod_p(1-r_p),\quad b_+:=\prod_p(1+r_p),\quad
 \kappa_B=b_+/b_-,
\]
with products over the fixed finite primes in \(S\). If
\[
 I-\sigma A_\infty\succeq g_{\infty,\sigma}I,
                 \quad\sigma\in\{+1,-1\},
\]
then
\[
 \boxed{I-\sigma A_S\succeq
             \kappa_B^{-2}g_{\infty,\sigma}I.}            \tag{15}
\]
Also
\[
 \boxed{1-\|A_S\|^2\ge
             \kappa_B^{-2}(1-\|A_\infty\|^2).}           \tag{16}
\]
These statements are uniform in discretization, not in growing \(S\). [ABSTRACT][PAPER]

**Proof.** For \(f\in\operatorname{ran}P\), put \(g=B_S^*f\). Both \(B_S^*\) and its inverse preserve this cutoff range: their shift expansions move only left on the log line. Moreover \(b_-\|f\|\le\|g\|\le b_+\|f\|\). Equation (14) gives
\[
 \langle g,(I-\sigma A_\infty)g\rangle
 =\tfrac12\|F_\infty g-\sigma g\|^2
 \le b_+^2\tfrac12\|F_Sf-\sigma f\|^2
 =b_+^2\langle f,(I-\sigma A_S)f\rangle.
\]
Apply the archimedean floor and the lower norm bound for \(g\). This proves (15).

For (16), use cutoff invariance to write
\((I-P)F_\infty g=(I-P)B_S^*(I-P)F_Sf\). The left side has squared norm at least \((1-\|A_\infty\|^2)\|g\|^2\); the right side has norm at most \(b_+\|(I-P)F_Sf\|\). Take the infimum over unit \(f\). QED.

There is an associated count comparison. For \(0<\varepsilon\) with \(\kappa_B^2\varepsilon<1\), let \(N_{S,\sigma}(\varepsilon)\) count eigenvalues of \(\sigma A_S\) strictly above \(1-\varepsilon\). The same subspace argument, in both directions, gives
\[
 N_{\infty,\sigma}(\varepsilon/\kappa_B^2)
 \le N_{S,\sigma}(\varepsilon)
 \le N_{\infty,\sigma}(\kappa_B^2\varepsilon).             \tag{17}
\]
The restriction keeps all counts away from the infinite zero cluster. This is a quantitative threshold relation, not “one direction per prime.” The Euler map is not an eigenvector map for the compressions: a cutoff commutator remains. The source count and exact limiting values in the reported two-mode cluster are not determined by the supplied uncertified eigenvalue table.

For \(S=\{\infty,2\}\), \(\kappa_B^2=17+12\sqrt2\). Thus an independently certified archimedean signed gap supplies a semilocal gap with an explicit finite loss. The observed archimedean numbers can guide that certificate; they are not substituted for its lower endpoints.

### Theorem 3. Density through the well-conditioned Euler Gram

Let \(P_0=\mathsf S_\infty\), \(\mathscr H_0=\operatorname{ran}P_0\), \(B=I-rU_a\), and
\[
 G=P_0B^*BP_0|_{\mathscr H_0},\qquad
 g_0=(1-r)^2,\quad g_1=(1+r)^2,
 \quad g_0I\preceq G\preceq g_1I.
\]
The Sonin-space isomorphism gives
\(\mathsf S_2=BP_0G^{-1}P_0B^*\). Choose an orthonormal basis \(b_j\) of \(\mathscr H_0\). The Fourier evaluation functional has Riesz vector \(w_\xi\), characterized by
\[
 \mathscr F f(\xi)=\langle w_\xi,f\rangle,
 \qquad \|w_\xi\|^2=k_\infty(\xi).
\]
The locally integrable spectral construction in [R] and its PHASEPROOF source supplies this vector almost everywhere; use its source-continuous evaluation representative where pointwise values are claimed. Then
\[
 \boxed{k_2(\xi)=|1-re^{-ia\xi}|^2
                      \langle w_\xi,G^{-1}w_\xi\rangle.} \tag{18}
\]
Consequently
\[
 \frac{|1-re^{-ia\xi}|^2}{g_1}k_\infty(\xi)
 \le k_2(\xi)\le
 \frac{|1-re^{-ia\xi}|^2}{g_0}k_\infty(\xi).              \tag{19}
\]
[ABSTRACT][PAPER]

**Proof.** \(BP_0G^{-1/2}\) is an isometry onto the semilocal Sonin space. Fourier transformation of \(Bf\) multiplies evaluation by \(1-re^{-ia\xi}\). Sum squared evaluations on the images of the orthonormal basis, or apply the Riesz functional to that isometry. This gives (18); functional calculus gives (19). Both sides of (19) are continuous source densities, so the inequalities extend from almost everywhere to every point. QED.

This is a genuine source representation without \((1-\lambda_{2,n}^2)^{-1}\). It does not pretend that obtaining the archimedean evaluation vector and its tail is free. That supplier is separate, fixed, and measurable; its error is not the unknown semilocal near-unit gap.

For example, if \(\|\widehat G-G\|\le\varepsilon_G<g_0\) and \(\|\widehat w-w\|\le\varepsilon_w\), then, with \(b=1-re^{-ia\xi}\),
\[
 \left|k_2-|b|^2\langle\widehat w,\widehat G^{-1}\widehat w\rangle\right|
 \le |b|^2\left[
 \frac{2\|\widehat w\|\varepsilon_w+\varepsilon_w^2}{g_0}
 +\frac{\varepsilon_G\|\widehat w\|^2}{g_0(g_0-\varepsilon_G)}\right].
 \tag{20}
\]
This follows by separating the vector error and the resolvent identity. Errors in \(b\) and in the subtracted \(q_2/(2\pi)\) must be added if they are also approximated. There is no dependence on \(\alpha_2\).

### Full-residual version for a finite evaluator

For any finite trial vector \(y\in\mathscr H_0\), define
\[
 E(y)=2\Re\langle w,y\rangle-\langle y,Gy\rangle,
 \quad z=w-Gy.
\]
Completing the square gives
\[
 \langle w,G^{-1}w\rangle=E(y)+\langle z,G^{-1}z\rangle,
\]
\[
 \boxed{|b|^2(E(y)+\|z\|^2/g_1)\le k_2
                  \le |b|^2(E(y)+\|z\|^2/g_0).}          \tag{21}
\]
All terms have finite, source-fixed coefficients. The residual is the full one:
\[
 \|z\|^2=k_\infty-2\Re\langle w,Gy\rangle+\langle y,G^2y\rangle.
 \tag{22}
\]
For a finite projection \(F\), evaluating the last term requires \(FG^2F\), not \((FGF)^2\). This is precisely the excursion guard in [PP2, Lemma 5]. Equation (21), with enclosures of (22), is a finite specification; no such calculation was run here. The purely algebraic error conversion is proved, while numerical source-vector/matrix suppliers remain conditional.

## 5. Q2(c): negative density, actual low-frequency information, and the missing error price

### 5.1 What is wrong in the current substitution into (6)

The true \(k_2\) is nonnegative. The current calculation mixes an exact source \(\gamma_2\), a much longer scalar \(t_2\) sum, a shorter nonunitary Fourier truncation for the operator/vector terms, and deletion of modes outside the contraction range. Thus it is not the exact density of a single pair of orthogonal projections. [OP; TS; DR] [FINITE_CELL][PAPER audit]

Both inverse-weighted terms in [R, (6)] can be wrong. The observed negative value does not identify one of them as the unique defective term. The failure is in the joint source approximation, and stable agreement between two such truncations does not remove the bias. In particular, deletion is not repaired by the words “no clipping, no rescaling.”

The positivity of an omitted **true** correction mode does not imply that the retained **approximate** correction is a lower bound for the true sum. Eigenvectors, eigenvalues and vector coefficients have all changed. Even in one dimension, with true \(A=0,c=1,t=0\), the true correction is zero. Using \(\widehat A=\varepsilon\), \(\widehat u=\varepsilon\), \(\gamma=1\), but retaining the true scalar term, produces the strictly positive correction \(2\varepsilon^2/(1+\varepsilon)\). It overestimates the true correction for arbitrarily small \(\varepsilon>0\). Hence a positive approximate correction cannot be added as a certified source lower bound without an error estimate. [ABSTRACT][PAPER]

Equation (20) or (21), not mode deletion, supplies the needed source error price. The new frame calculation can also preserve nonnegativity of its *computed* approximation; proving that it approximates the intended source still requires the stated residual/enclosures.

### 5.2 What is not known on [5,16]

The supplied data do not certify the sign of \(d_2\) throughout \([5,16]\). The exact implication is only
\[
 d_2(\xi)\ge-q_2(\xi)/(2\pi).
 \tag{23}
\]
Where \(q_2<0\), this forces \(d_2>0\). Where \(q_2\ge0\), either sign remains possible until an upper or lower density envelope decides it. The reports' rounded zeros of \(k_\infty\) likewise do not prove exact vanishing on an interval.

### 5.3 A strict source-positive point inside the disputed interval

There is a paper-only check independent of the bad semilocal inverse. Put \(\xi_*=2\pi/a\in(5,16)\). Then
\[
 q_2(\xi_*)=q_\infty(\xi_*)-2a(1+\sqrt2).
\]
For \(x=1/4,y=\pi/a<5\), the digamma partial-fraction expansion [DLMF 5.7.6] gives
\[
 \Re\psi(x+iy)-\psi(x)
 =\sum_{n\ge0}\frac{y^2}{(n+x)((n+x)^2+y^2)}
 <4+\tfrac12\log(1+16y^2).
\]
The bound follows by separating \(n=0\) and comparing the remaining decreasing summand with its integral from \(x\) to infinity. Use
\(\psi(1/4)=-\gamma_E-\pi/2-3\log2\), obtained by reflection and duplication. The elementary bounds \(\log2>2/3\), \(\pi/2>3/2\), \(\log\pi>1\), and \(\frac12\log401<7/2\) give \(q_\infty(\xi_*)<3\). Also \(2a(1+\sqrt2)>16/5\). Hence
\[
 \boxed{q_2(\xi_*)<-1/5,\qquad d_2(\xi_*)>1/(10\pi)>0.} \tag{24}
\]
This extends to some neighborhood by continuity. It does not classify the entire interval or certify the reported negative bands. [ABSTRACT][PAPER]

### 5.4 Small low-frequency mass is not exact insensitivity

For a band \(B\), the correct error inequality is
\[
 \left|\int_B W_h(d_2-\widehat d_2)\right|
 \le\int_B W_h\varepsilon_d
 \le\mu_B\sup_B\varepsilon_d,
 \quad\mu_B=\int_BW_h.
 \tag{25}
\]
A nonzero compact smooth \(h\) has an entire transform with isolated real zeros. Apart from those and the discrete zeros of the lobe factor, its weight is positive. Thus a band of positive length has positive mass, not exactly zero. A reported fraction \(0.05\%\) of the total mass \(2\pi\) would correspond to \(\mu_B=\pi/1000\), before its own numerical error. An uncontrolled error of order one on that band is not negligible compared with the proposed plant margins.

A source bound independent of the semilocal inverse is available from (19):
\[
 |d_2(\xi)|\le |q_2(\xi)|/(2\pi)
       +|1-re^{-ia\xi}|^2 k_\infty(\xi)/g_0.
 \tag{26}
\]
Combine its certified band supremum with (25). Without that bound, the assertion “the low-frequency obstruction is irrelevant” is unproved. [ABSTRACT][PAPER]

## 6. Q3: the false factor shifts the infimum, not merely some sample values

Keep the actual Sonin projection fixed, as required by the plant. Its exact arithmetic increment on normalized minus tests is \(-\delta_M\), where
\[
 \delta_M=2a(\cosh(a/4)-1)>0.
\]
Therefore
\[
 \boxed{\mathfrak m_\sharp(h)=\mathfrak m(h)-\delta_M,
 \qquad \inf_h\mathfrak m_\sharp=
                      \inf_h\mathfrak m-\delta_M.}        \tag{27}
\]
The same nonzero class and normalization occur in both infima. They cannot both equal zero. [ABSTRACT][PAPER]

Choose any nonzero \(\eta\in C_c^\infty(I)\) and the exact pole-null family
\[
 h_T=(\partial_x^2-1/4)(e^{iTx}\eta(x)).
\]
Its two moments vanish by integration by parts. Moreover \(H_T/T^4\to\|\eta\|^2\) and
\(\widehat h_T(\xi)=-(\xi^2+1/4)\widehat\eta(\xi-T)\).
Since \(d_2\) and \(\ell_2\) are bounded and tend to zero at infinity, dominated convergence after \(\xi=T+s\) gives
\[
 \mathfrak m(h_T)\longrightarrow0,\qquad
 \mathcal F(h_T)\longrightarrow0.                         \tag{28}
\]
Domination uses rapid decay of \(\widehat\eta\) and the bound
\(((T+s)^2+1/4)^2/T^4\le C(1+|s|)^4\) for \(T\ge1\), with the lobe factor at most two. This rechecks the load-bearing limit in [R, (36)] without using observed exponents.

Thus \(\inf\mathfrak m\le0\), and the planted infimum is at most \(-\delta_M\). If the genuine class inequality is subsequently proved, the two infima are **0 and \(-\delta_M\)**. Without that sign proof, the genuine infimum could be negative. In either case,
\[
 \mathfrak m_\sharp(h_T)<-\delta_M/2
                       \quad\text{eventually}.            \tag{29}
\]
This is a strict negative upper-envelope witness family for the planted source. It proves whole-class plant detection, not the true-source class sign. It also rules out a fixed positive margin on the whole original class. [ABSTRACT][PAPER]

Test-dependent survival is exactly what (27) predicts: detection occurs when \(\mathfrak m(h)<\delta_M\), survival when \(\mathfrak m(h)\ge\delta_M\). That is compatible with a useful arithmetic discriminator. It is not, by itself, a theorem identifying zeta among all functions or a replacement for an exhausting test-class argument.

### What would certify the three reported outcomes?

For rigorous intervals \([L_m,U_m]\) and \([L_\delta,U_\delta]\):

| Claim | Required direction |
|---|---|
| Genuine test is nonnegative | \(L_m\ge0\). |
| Plant has strictly negative margin | \(U_m<L_\delta\). |
| Plant survives | \(L_m\ge U_\delta\); strict inequality gives a positive margin. |
| Either interval overlaps its threshold | Inconclusive. |

The frozen-test flip requires an **upper** bound. Omitting nonnegative true corrections would go in the opposite direction and cannot certify that flip. The proposed \(h_4\) scalar floor near \(0.0035\), even after certification, is below \(\delta_M\); it alone would not certify survival. Ten times a consecutive-\(J\) difference is not a proved error bound. The claimed flip for the frozen bump and survival for \(h_2,h_4\) are therefore retained as diagnostics, not ratified finite results. [FINITE_CELL][CONDITIONAL]

## 7. Q4: smallest proved theorem and an explicit inverse-free certificate specification

### 7.1 The smallest theorem already proved

On every smooth compact test for which the source trace identity applies, (5) holds. On the exact pole-null minus class, (6) holds. In particular,
\[
 \mathcal F(h)\ge0\ \Longrightarrow\
 Q(v_h)=L_2(v_h)\ge n_2(v_h)\ge0.                         \tag{30}
\]
The implication and its source minorant are **PAPER theorems**; its scalar sign is an unproved input. No proof of \(\mathfrak m(h_4)\ge0.0035\), or of \(\mathfrak m\ge\mathcal F\ge0\) on the whole class, is present in the shelf. This audit supplies neither as a numerical result. The square identity is an actual new derivation here, not merely a receiver name.

In particular, [TS] says its tail bound uses the shape constant **set to 1**. [R] states that the constant must be proved, and [RI] reports empirical constants rather than a uniform proof. It follows that the displayed \(3.5\cdot10^{-8}\) is not yet the claimed rigorous tail supplier. This is missing justification, not a claim that the literal numerical tail necessarily exceeds that number. An incomplete-gamma formula is exact as an identity; its finite-precision evaluation and differentiation are not automatically enclosures. [PAPER audit of TS, RI]

### Theorem 4. An explicit coarse scalar tail bound

For every \(\beta\ge1\) and every real \(\xi\),
\[
 \boxed{|J(\beta,\xi)|\le
             256\,\beta^{-1/2}(1+\log\beta).}             \tag{31}
\]
This deliberately conservative constant is sufficient to make the scalar-series truncation certifiable without fitting an oscillatory constant. [ABSTRACT][PAPER]

**Proof.** Substitute \(y=\beta v\), expand the cosine, and discard the unit-modulus factor \(\beta^{-i\xi}\). Apart from \(\beta^{-1/2}\), the two integrals have amplitude
\(b(y)=y^{-1/2}\log(\beta/y)\ge0\) on \(0<y\le\beta\), and phase \(\phi(y)=\pm y+\xi\log y\).
The part \(0<y<1\) is at most \(2\log\beta+4\).

Partition \([1,\beta]\) into dyadic intervals \([B,2B]\), possibly truncating the last. If \(|\xi|<B/2\) or \(|\xi|>4B\), the monotone phase derivative has modulus at least \(1/2\). Integration by parts bounds every unweighted subinterval primitive by 8. Since \(b\) decreases, partial integration against that primitive bounds the weighted integral by \(8B^{-1/2}\log\beta\). Sum the geometric series.

On each remaining interval, \(|\phi''|\ge1/(8B)\). The elementary second-derivative bound gives every unweighted primitive modulus at most \(8\sqrt{8B}\). For completeness, split where \(|\phi'|\le\sqrt\lambda\), with \(\lambda=1/(8B)\): this set has length at most \(2/\sqrt\lambda\); on the two complements integration by parts gives together at most \(6/\sqrt\lambda\). This proves the constant 8. Multiplication by the decreasing amplitude bounds each such weighted interval by \(16\sqrt2\log\beta\). There are at most four dyadic intervals with \(B/2\le|\xi|\le4B\).

The resulting bound is
\[
 \beta^{-1/2}\left[4+
 \left(2+\frac8{1-2^{-1/2}}+64\sqrt2\right)\log\beta\right],
\]
which is smaller than (31). Averaging the two exponential integrals introduces no additional factor. QED.

For \(p=2\), \(\beta_j=2\pi2^j\), \(c_{-1}=-1/2\), \(c_j=1/2\) for \(j\ge0\). If the sum is retained through \(j=J\), (31) gives, **uniformly in \(\xi\)**,
\[
 |t_2-t_2^{[J]}|\le\varepsilon_J:=
 \frac{128}{\pi\sqrt{2\pi}}r^{J+1}
 \left[\frac{1+\log\beta_{J+1}}{1-r}
                         +\frac{ar}{(1-r)^2}\right].      \tag{32}
\]
Thus its contribution to the normalized floor error is at most
\[
 \boxed{4\pi\varepsilon_J.}                              \tag{33}
\]
This uses \(\int W_h=2\pi\) and \(|\gamma_2|=1\). The bound is not claimed sharp, and no chosen \(J\) was evaluated in this audit. It closes the *form* of the missing constant supplier; independent paper checking remains appropriate.

One also obtains an explicit global bound \(|t_2|\le T_*\) by summing (31):
\[
 T_*:=\frac{128}{\pi}\left[
 \frac{1+\log\pi}{\sqrt\pi}
 +\frac1{\sqrt{2\pi}}\left(
      \frac{1+\log(2\pi)}{1-r}+\frac{ar}{(1-r)^2}\right)\right].
 \tag{34}
\]
Hence \(|\ell_2|\le2T_*\). This is usable, although conservative, for frequency-tail and smooth-approximation budgets.

### 7.2 Freeze the actual test, including its regularity

The reported polynomial profiles are not \(C_c^\infty(I)\). The zero-extended \(\eta_4=(1-(x/\delta)^2)^4\) is only finitely smooth; \(h_4=\eta_4''-\eta_4/4\) is \(C^1\), not \(C^\infty\). For \(k=2\), \(h_2\) has endpoint jumps. Even the frozen exponential bump, though globally smooth, has closed support \([-\delta,\delta]\), not a compact subset of the open interval \(I\). These are valid approximation profiles, not literal members of the strict class by terminology alone.

Both moments of \(h_k\) still vanish exactly: \(\eta_k\) and \(\eta_k'\) vanish at both endpoints, so two integrations by parts have no boundary term. The normalized functional is invariant under the nonzero scalar \(N_k\), so it is permissible to certify the same profile with \(N_4=1\), explicitly recording that cancellation.

For a direct exact norm supplier put \(z=x/\delta\) and
\[
 h_4(x)=\sum_{j=0}^4 A_jz^{2j},\quad |x|<\delta,
\]
\[
 (A_0,A_1,A_2,A_3,A_4)=
 (-8\delta^{-2}-1/4,\ 72\delta^{-2}+1,\
 -120\delta^{-2}-3/2,\ 56\delta^{-2}+1,\ -1/4).
\]
Then
\[
 H_4=2\delta\sum_{i,j=0}^4\frac{A_iA_j}{2(i+j)+1}.        \tag{35}
\]
The Fourier transform follows by integrating this finite polynomial against \(e^{-i\delta\xi z}\), using its Taylor value at \(\xi=0\) rather than dividing by a removable zero. This removes any fitted norm or imported FFT row. [ABSTRACT][PAPER]

The profiles belong to the logarithmic form domain needed here: \(h_4\in H^1\), and the piecewise smooth \(h_2\in H^s\) for \(0<s<1/2\). The bound \(k_2\le C(1+\log(2+|\xi|))\), from (19) and the archimedean source estimates, ensures convergence of the separate \(n_2\) and \(L_2\) integrals under approximation in that domain. Smooth, slightly compressed mollifications of \(\eta_k\), followed by \(\partial^2-1/4\), preserve both moments and put the approximants strictly inside \(I\). Thus the trace identities extend to these profiles; a positive floor with a controlled approximation error transfers to actual smooth tests. This extension is stated explicitly, not used to hide a class change.

### 7.3 Complete finite certificate budget

Choose a frequency cutoff \(X\), scalar-series cutoff \(J\), and an interval enclosure for the compact-frequency integral. Enclose \(H>0\), \(\widehat h\), \(\gamma_2\), and every retained \(J(\beta_j,-\xi)\); the incomplete-gamma branch and its parameter derivative must match the defining integral. Scalar evaluation error is distinct from quadrature error. If \(|t-\widehat t|\le e_t\) and \(|\gamma-\widehat\gamma|\le e_\gamma\), then
\[
 |\ell-2\Re(\widehat\gamma\widehat t)|
       \le2(e_t+e_\gamma|\widehat t|).                    \tag{36}
\]
The \(e_t\) term must include (32) unless the series tail is budgeted separately. Do not count it twice.

For the omitted frequency mass \(\mu_X=\int_{|\xi|>X}W_h\), (34) gives a floor-tail bound \(2T_*\mu_X\). An analytic mass bound, independent of sampled coverage, is for example
\[
 \mu_X\le\frac{4\pi\|h^{(s)}\|_2^2}{H X^{2s}},
                 \qquad h\in H^s,\ s\text{ a positive integer}.
 \tag{37}
\]
It follows from Plancherel and \(1-\cos\le2\). Use \(s=1\) or \(2\) for \(h_4\), with its actual weak derivatives and exact polynomial integrals. For a bounded-variation jump test, \(|\widehat h(\xi)|\le\operatorname{TV}(h)/|\xi|\) gives the alternative
\(\mu_X\le4\operatorname{TV}(h)^2/(HX)\). Sharper proved tail bounds are allowed; empirical coverage is not a replacement.

A valid output is an interval
\[
 [L_F,U_F]\supset\mathcal F(h),
\]
whose error ledger separates normalization/transform evaluation, gamma and Mellin evaluation, compact-frequency quadrature, scalar-series tail, and frequency tail. With uniform scalar-tail accounting one may use
\[
 L_F=F_{\rm compact,low}
       -E_{\rm scalar}-E_{\rm quadrature}
       -4\pi\varepsilon_J-2T_*\mu_X,
 \tag{38}
\]
provided \(F_{\rm compact,low}\) already handles the remaining interval-valued inputs and there is no double-counting. If \(L_F>0\), Theorem 1 certifies \(\mathfrak m(h)\ge L_F\), with **no semilocal inverse error**. If \(U_F<0\), only the sufficient scalar condition is refuted on that test; the positive correction in (6) must still be examined before refuting \(\mathfrak m\ge0\).

A prospective acceptance target for the reported \(h_4\) is \(L_F\ge1/500\). This rational target is chosen below the reported diagnostic floor, not claimed achieved. For the frozen bump, a separate budget must use its own exact profile; it cannot be scored using \(h_4\).

After a certified smooth unit test \(h_*\) has \(\mathcal F(h_*)\ge c>0\), an explicit infinite-dimensional neighborhood follows. The operator norm in (11) is at most \(2\pi\|\ell_2\|_\infty\) on the supported class, by (2). If \(M\) is this bound, then every pole-null supported \(h\) with \(\|h-h_*\|\le\varepsilon\) satisfies
\[
 \mathcal F(h)\ge
 \frac{c-M(2\varepsilon+\varepsilon^2)}{(1+\varepsilon)^2}>0
 \tag{39}
\]
when the numerator is positive. This is a conditional consequence of a genuine positive certificate, not a subclass proved positive by the current diagnostic values.

**Conclusion for Q4:** the classwide minorant and its squared remainder are proved on paper; the inverse-free finite sign certificate is now explicitly specified. The supplied \(0.0035\) number is not yet such a certificate. No “first prime-carrying positivity theorem past the archimedean window” is claimed without the missing scalar lower endpoint.

## 8. Prediction ledger: frozen events, not renamed events

All prediction rows below have scope **ABSTRACT**, verifier **PAPER** as an assessment of the stated event. Numerical subevents retain **FINITE_CELL / CONDITIONAL** status where no enclosure exists.

| Observer prediction | Frozen p | Fate and exact boundary |
|---|---:|---|
| P_FLOOR_LEMMA_THEOREM | 0.85 | CONFIRMED_ON_PAPER. Equations (4)--(8) prove the true-source result; no eigenvalue experiment is needed. |
| P_SCALAR_CONDITION_ON_CLASS | 0.30 | NOT_ACHIEVED_IN_THIS_BATCH. Equation (9) remains open; its mathematical negation is not asserted. |
| P_SCALAR_CONDITION_ON_SUBCLASS | 0.50 | NOT_ACHIEVED_IN_THIS_BATCH. Equation (39) still requires a certified positive seed. |
| P_TWO_UNIT_ANGLES_SOURCE_FEATURE | 0.65 | NOT_CONFIRMED. Exact ±1 limits are refuted; a two-near-unit count and its proposed Euler-image/count-growth explanation remain unproved. Do not score the compound event from a fitted cluster. |
| P_STABLE_REPRESENTATION | 0.50 | CONFIRMED_ON_PAPER, SOURCE-SPECIFIC. Equations (18)--(22) have no semilocal angle denominator; archimedean evaluation and full-residual suppliers are explicit, not free. |
| P_K2_NEGATIVE_IS_TRUNCATION | 0.80 | CONFIRMED as incompatibility with the true nonnegative source density. The exact division of blame between approximation terms remains unresolved. |
| P_PLANT_TEST_DEPENDENCE_EXPECTED | 0.60 | REFUTED_AS_COMPOUND. Test dependence is expected, but its stated pair of zero infima is impossible by (27). The correct conditional infima are 0 and minus delta_M. |
| P_SMALLEST_THEOREM_IS_FINITE_TEST | 0.70 | NOT_REALIZED. The proved result is a classwide minorant identity; no finite h_4 interval certificate has been supplied. |

### Prior judge registrations explicitly requested for rescoring

| Frozen prior registration | p | Fate |
|---|---:|---|
| P_PHASEPROOF_SOURCE_PACKET_MINUS_MARGIN_POSITIVE | 0.70 | UNRESOLVED. [PP2] requires a **complete source-valid enclosure** for the exact earlier eta test. Positive diagnostics and a scalar floor computed with an unproved tail constant do not meet that event. The forecast did not predict a 0.34-sized margin. |
| P_R_PERIODIZATION_SURVIVES | 0.99 | CONFIRMED_ON_PAPER: (10), the independent check, and the support/autocorrelation proof agree. A numerical check alone would not have discharged its quantifiers. |
| P_R_SOURCE_REMAINDER_DECAYS | 0.76 | PAPER_DERIVATION_RETAINED_AFTER_RECHECK. The source Mellin split gives the exponents used in (28); observed slopes corroborate, not prove them. No sharp leading constant or certified pointwise table follows. |
| P_R_PEAK_NOTCH_AND_POSITIVE_ATOM | 0.97 | CONFIRMED_ON_PAPER. The exact polynomial and atom computation survives the independent check. No favourable full reservoir sign is added to that event. |
| P_R_LOG_GAIN_FAILS | 0.94 | CONFIRMED_ON_PAPER at its original uniform-scaling theorem-shape scope. The source high-modulation limit, not the finite carrier, supplies the counterexample. |

The statements made before this audit's tests were that the floor algebra should hold and that the unit-angle limits and plant infimum needed separate checks. The first is confirmed; the latter checks produced the explicit corrections above. No probability is retroactively assigned to those conversational registrations.

### New prospective registrations

These concern future independent checking or a future certificate, not experiments performed here.

```yaml
P_SF_SQUARE_AND_PACKET_IDENTITY_SURVIVES:
  probability: 0.97
  event: independent_review_accepts_4_to_8_with_the_same_source_trace_domain
  fate: PENDING
P_SF_BSTAR_GAP_AND_GRAM_TRANSFER_SURVIVES:
  probability: 0.90
  event: independent_review_accepts_15_to_22_without_a_semilocal_angle_gap_supplier
  fate: PENDING
P_SF_EXPLICIT_J_MAJORANT_SURVIVES:
  probability: 0.91
  event: uniform_bound_31_and_tail_32_hold_with_constant_256_as_written
  fate: PENDING
P_SF_H4_SCALAR_CERTIFICATE_POSITIVE:
  probability: 0.75
  event: full_source_scalar_enclosure_for_the_exact_h4_profile_has_L_F_at_least_1_over_500
  prerequisites: all_errors_in_38_and_the_form_domain_extension_are_checked
  fate: PENDING_NO_RUN_IN_THIS_AUDIT
```

## 9. Route map, dependency epistemics, and one next directive

### Two representations before escalation

| Representation | What it decides | Kill-power / cost estimate | Main risk |
|---|---|---|---|
| Inverse-free scalar floor, explicit J-tail, (31)--(38) | Whether a declared exact test obtains a genuine positive source minorant | 9/10 / 3/10 | Unproved quadrature or transform tail disguised as an exact formula. |
| Euler-Gram evaluation and full residual, (18)--(22) | True pointwise density and two-sided test/plant margins without the semilocal angle inverse | 9/10 / 6/10 | Uncertified archimedean evaluation vector or replacing FG²F by (FGF)². |

These are ordinal estimates, not measured runtimes or authorizations for a larger run. The compact test-space operator (11) remains the whole-class representation; it needs a real complement/sign argument rather than progressively larger unproved tables.

### Strongest attack

The strongest objection to a positivity announcement is still decisive: **a proved lower-bound formula is not a proved nonnegative lower endpoint**. Moreover, the current retained-mode calculation is not even a source lower envelope, and an upper envelope is essential for the claimed frozen-test plant flip. The repaired statement is Theorem 1 plus a separately certified scalar or full-residual inequality, not a weakened declaration that the diagnostics “look stable.”

### Consumer-first dependency record

**DOWNSTREAM_CONSUMER:** `published_Weil_criterion_on_all_complex_compact_smooth_tests`.

**ACTUAL_CONSUMER_REQUIREMENT:** nonnegativity of the actual Weil form on that entire test class. Its intermediate target here is the exact pole-null two-lobe minorant at cutoff one.

**ORIGINAL_REQUESTED_OBJECT:** a nonnegative scalar floor on the whole phase class, stable semilocal conditioning, and certified plant interpretation.

**ORIGINAL_OBJECT_IS:** `NOT_NECESSARY`. The scalar floor is sufficient, not necessary, even for the restricted minorant: a negative floor may be repaired by the positive square in (6). The restricted two-lobe class is not proved necessary or exhaustive for the global consumer.

**KNOWN_WEAKER_INTERFACES:** a nonnegative full value of (6) without separate scalar positivity; an exact finite-packet lower matrix plus a proved complement/coupling estimate; or direct positivity of the unchanged full Weil form. The first reaches only the declared tests; the second reaches a class only after its complement theorem; none supplies the global consumer without the original all-test quantifier.

**FAILURE_TYPE:** `NO_DERIVATION` for (9) and the numerical enclosures; `INCOMPATIBILITY` for exact unit-angle limits at fixed cutoff; `COUNTEREXAMPLE` for applying the mode sign to a noncontraction, for certifying approximate retained corrections by positivity alone, and for the assertion that both planted and genuine infima are zero.

**EPISTEMIC_STATUS:** the scalar sign and the finite numerical margins are `RESEARCH_DEBT`. Only the exact incompatible theorem shapes are rejected. No `ROUTE_FAMILY` death is claimed. The request commit, [OP]/[TS] blobs and equations (4), (15)--(17), (27)--(29) are the pinned evidence boundary.

**NOVELTY_AXIS:** extract the exact positive square already present in the source, then change the density evaluation to the bounded Euler Gram. Historical priority is not asserted.

**REOPEN_TRIGGER:** for finite-sign debt, a complete lower/upper interval ledger (38) or (21); for the whole scalar class, a proof or a certified smooth negative direction for (11); for the near-unit count, a threshold-separated source spectral enclosure. No larger J-table by itself is a reopen trigger.

**MINIMAL MISSING IDENTITY / INEQUALITY:** for the next finite result, `L_F(h_4) > 0` with every error in (38). For the whole class, `T >= 0` for the unchanged compact operator (11). For a planted flip, `U_m(h) < L_delta_M`, not merely a positive original floor.

### Exactly one CODEX DIRECTIVE — prospective, not executed here

**Target:** independently check and then supply one inverse-free scalar-floor certificate for the exact zero-extended polynomial profile \(h_4\) in §7.2. Use its explicit regularity extension; do not silently substitute a bump and rescore the frozen PHASEPROOF event.

**Inputs:** the request pin; source \(\gamma_2,t_2\) from [R]; Theorem 1 and equations (31)--(38); the exact coefficient/norm formula (35).

**Proof route:** validate the projection-square identity and the explicit scalar-tail constant first. Evaluate only the scalar compact-frequency integral with outward error bounds, attach a proved frequency tail and positive norm enclosure, and return \([L_F,U_F]\). No \(A_2\) diagonalization, spurious-mode deletion, empirical tail constant, or carrier rescaling is needed.

**Success:** `SCALARFLOOR_H4_SOURCE_LOWER_CERTIFIED`, with \(L_F\ge1/500\) and the exact profile/domain recorded. This certifies that test's genuine-source positivity only; it does not certify plant survival, the frozen eta event, or the whole class.

**Failure:** `SCALARFLOOR_CONSTANT_OR_QUADRATURE_UNCERTIFIED`, `SCALARFLOOR_H4_ZERO_STRADDLE`, or `SCALARFLOOR_H4_SUFFICIENT_CONDITION_NEGATIVE`. The last code refutes only the sufficient floor on this test unless an upper bound for the complete margin is separately negative. Supply the exact first failing bound rather than increasing a large carrier.

**Boundary:** no run or Lean edit was performed or initiated by this verdict. A later numerical execution requires the observer's normal transaction boundary. No `lake` command is applicable to this document-only adjudication.

## 10. Closeout and publication handoff

What became smaller is exact: the source floor has a universal projection-square proof; the semilocal density can use an Euler Gram with a known lower bound; an explicit, non-fitted scalar tail budget replaces an unspecified constant. What remains is a signed scalar integral or, for a whole-class result, the compact test-space positivity problem (11).

Do not repeat: exact ±1 limits from noncontractive truncations; one angle per prime without a threshold theorem; an omitted approximate mode as a true lower certificate; two zero infima under a nonzero constant shift; or “exact special-function formula” as a substitute for error-controlled evaluation. Small-band mass must always be multiplied by a proved error envelope.

```yaml
META_CLOSEOUT:
  PROGRESS_CLASS: PROOF_PROGRESS
  COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
  ROUTE_SCORE: 5
  iteration:
    target: SCALARFLOOR_source_floor_and_conditioning
    status: PROGRESS
    failed_strategy: certify_source_margins_from_retained_noncontractive_truncation_modes
    cognitive_operator_used: REPRESENTATION_SHIFT
    new_gap_name: complete_inverse_free_scalar_floor_lower_enclosure
    invariant_learned: D_plus_D_squared_equals_PQ_plus_QP_and_the_positive_remainder_is_source_exact
    forbidden_future_move: turn_J_spread_or_a_set_to_one_tail_constant_into_a_certificate
    next_decisive_test: independently_checked_h4_scalar_interval_lower_endpoint
PUBLICATION_HANDOFF:
  BRANCH: rh_clean
  PATHS_WRITTEN:
    - docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SCALAR_FLOOR_AND_SEMILOCAL_CONDITIONING_2026-09-07.md
  LEAN_FILES_WRITTEN: []
  LEAN_BLOB_HASHES: []
  LEAN_GATE_COMMANDS: NOT_APPLICABLE_DOCUMENT_ONLY
  EXPECTED_AXIOM_PROFILE: NOT_APPLICABLE_NO_KERNEL_RESULT_CLAIMED
  COMMIT_AND_READBACK_BLOB: reported_in_the_closing_publication_receipt
  READBACK_CHANGES: confirms_document_publication_only_not_mathematical_verification
```

Only this verdict document is to be published. Request bytes, prior verdicts, scripts, predictions, queue and route state remain untouched. New derivations have verifier **PAPER** and await independent review. A successful hash/readback receipt does not change that verifier.

## 11. Independent second-pass addendum — 2026-09-07

```yaml
ADDENDUM_KIND: APPEND_ONLY_SECOND_PASS
OPERATIVE_CLASS: TRY_SCALAR_FLOOR_SQUARE_IDENTITY_AND_EULER_GRAM_CERTIFICATION
REQUEST_ID: REQ-2026-09-07-SCALARFLOOR
PRESERVED_BASE_BLOB: 9a96b510e7b35e30ffea982b4f14497b6d82584c
REQUEST_SHA256_RECOMPUTED_THIS_PASS: 727572551491e9a4374172c24ba1c2b7d16224f8f0263bc0bcd97a5ac5d3cbc7
REQUEST_GIT_BLOB_RECOMPUTED_THIS_PASS: fbfc4ce550a5716a77415b589cfd33d4631a919b
REQUEST_BYTES: 14243
REQUEST_LINES: 111
REQUEST_FINAL_LF: true
RESULT:
  Q1a: PROVED_ON_CLASS
  Q1b: PARTIAL_WITH_PRECISE_REMAINDER
  Q1c: PROVED_ON_CLASS
  Q2a: PARTIAL_WITH_PRECISE_REMAINDER
  Q2b: PROVED_ON_CLASS
  Q2c: PARTIAL_WITH_PRECISE_REMAINDER
  Q3: PARTIAL_WITH_PRECISE_REMAINDER
  Q4: COMPUTATION_SPECIFIED
ADDITIONAL_RESULT: MONOTONE_INVERSE_FREE_POSITIVE_CORRECTION_HIERARCHY
CLOSES_ANALYTIC_RH_SUPPLIERS: []
OPENS: []
SCOPE: ABSTRACT
VERIFIER: PAPER
NUMERICAL_RUN_PERFORMED: false
LEAN_EDIT_PERFORMED: false
BLIND_SECOND_REVIEW_CLAIM: false
PREDICTIONS_OR_PRIOR_TEXT_REWRITTEN: false
RH_CLAIM: false
```

The existing verdict is retained in full. This pass independently fetched and rehashed the controlling request, read the pinned evaluator report, PROGRESS, `evald.py`, `prod_op.py`, `prod_t.py`, and `final.py`, and checked the projection algebra and the Euler-Gram construction. The existing verdict's title was seen at intake; its full text was read before this closeout. This is therefore a separate mathematical recheck, not a blinded replication. The first verdict's source-reading and verification declarations above describe that first pass, not additional actions claimed for this one. No empirical table or post-request computation is used as a mathematical premise.

The primary crosswalk was checked against CCM arXiv:2310.18423v2, (57)--(59) and Theorem 4.6, including PDF pages 22--23. Those statements supply the multiplier and bounded invertible Sonin map, not the scalar sign. The requested CC20 and C26 versions were opened for their trace conventions. No new result from math/9811068v1 is imported. The attached historical route summaries are not evidence for this request.

### 11.1 Rechecked decisions for all four questions

**Q1.** The floor theorem and the stronger square identity (4)--(8) are correct on the stated tested trace domain. The real/imaginary proof (7) is preferable to expanding the generalized Mellin wave itself in an unproved absolutely summable eigenseries. In particular the exact lower bound is `m >= F`; a positive floating-point value of `F` is a separate claim requiring an enclosure. The whole-class scalar sign (9) remains unproved. The additional hierarchy below provides a weaker sufficient condition without requiring that scalar sign separately.

**Q2.** The fixed-cutoff operator cannot have the alleged exact limiting eigenvalues ±1. The source signed-gap transfer (15), concentration-gap transfer (16), and threshold-count statement (17) survive rechecking. The data still do not certify a two-mode count at a stated threshold. The representation (18)--(22) removes the semilocal angle denominator with explicit source constants, while retaining the archimedean evaluation-vector error. Small low-frequency mass is a weighted error allowance, never exact irrelevance.

**Q3.** Equation (27), not two zero infima, is the correct class statement. The planted and true margins differ by exactly `-delta_M`. The high-modulation family proves eventual detection of this fixed arithmetic mutation under the retained source remainder theorem. None of the three individual reported outcomes has a source-valid interval certificate. In particular a certified scalar *lower* floor would not certify the frozen-test plant *upper* inequality.

**Q4.** The inverse-free finite certificate specification is sound; the claimed value `m(h_4) >= 0.0035` is not presently a theorem. The explicit constant 256 in (31) is valid by the displayed dyadic proof: at most four stationary dyadic intervals occur, and the quoted sum of constants is below 256. The tail errors (32)--(38) must still be evaluated with directed bounds. The zero-extended polynomial profiles require the regularity and strict-support repair already stated in §7.2.

All four determinations are **PAPER**, not `LEAN` or `ARB_INTERVAL`. The strict positive point (24) does not determine the sign on an interval, and observed vanishing at precision 1e-16 does not establish an exact spectral gap in a density.

### 11.2 Theorem 5: a monotone polynomial hierarchy for the positive correction

This is an additional derivation, not a numerical test. It preserves the same source, test class, cutoff, and normalization. Fix a frequency and abbreviate the objects of (7) by `A,u,gamma,X,Y`. Put
\[
 H_-=(I-A)/2,\qquad H_+=(I+A)/2,
\]
\[
 c_d(\xi)=\sum_{j=0}^{d}
 \left(\langle X,H_-^jX\rangle+
       \langle Y,H_+^jY\rangle\right),\qquad d=0,1,2,\ldots .
 \tag{40}
\]
These `H_±` are positive contractions, not orthogonal projections. Then
\[
 \boxed{\|u\|^2=c_0\le c_1\le\cdots\le\ell_S-d_S,
       \qquad c_d\longrightarrow\ell_S-d_S.}             \tag{41}
\]
In particular, for the same phase test,
\[
 \boxed{\mathcal F(h)+\int W_hc_d\le\mathfrak m(h),
 \qquad \mathcal F(h)+\int W_hc_d\uparrow\mathfrak m(h).} \tag{42}
\]
[ABSTRACT][PAPER]

**Proof.** Since `||A||<1`, both `H_±` have norm less than one. The convergent geometric identities are
\[
 2(I+A)^{-1}=\sum_{j\ge0}H_-^j,\qquad
 2(I-A)^{-1}=\sum_{j\ge0}H_+^j.
\]
Each summand is positive. Apply (7) to obtain (41). The correction is integrable on each specified test; the bounds (12) and the source Mellin estimates provide a majorant. Monotone convergence proves (42). Neither a numerical lower bound for `1-||A||` nor an approximate eigenbasis is needed to establish any finite lower bound. QED.

For evaluation without a half-phase branch, (40) has the equivalent polynomial expression
\[
 c_d=\frac12\sum_{j=0}^{d}\left[
 \langle u,(H_-^j+H_+^j)u\rangle+
 \Re\{\gamma\langle u,(H_-^j-H_+^j)\bar u\rangle\}\right].
 \tag{43}
\]
Its first two levels are
\[
 c_0=\|u\|^2,\qquad
 c_1=\tfrac32\|u\|^2-\tfrac12\Re\{\gamma\langle u,A\bar u\rangle\}.
 \tag{44}
\]
Thus the first strengthening already retains the scalar-vector quantity `||u_S(xi)||^2`, without any operator inverse. Higher levels use only finite powers of the actual compressed Fourier operator. This does not authorize using powers of a different clipped operator.

There is also a one-sided frequency cutoff. Define
\[
 F_{d,X}(h)=\mathcal F(h)+\int_{|\xi|\le X}W_h(\xi)c_d(\xi)\,d\xi.
\tag{45}
\]
Then `F_{d,X} <= m`; it increases when either cutoff increases. In particular, the omitted **positive correction tail** need not be estimated to obtain a lower certificate. The scalar floor's own full-frequency tail still must be paid. This distinguishes the two tails that were combined in the report's claimed total error.

If a fixed true test has `m(h)>0`, there exist finite `d` and `X` with `F_{d,X}(h)>0`. Indeed first use (42), then monotone convergence in `X`. This is completeness of this hierarchy for a strictly positive individual test, not a proof that the selected test is positive and not a bound on the required depth. For a finite packet the unnormalized matrices obey the same Loewner monotonicity. Strict positivity of the true packet implies positivity at some finite depth/cutoff by finite-dimensional norm convergence; semidefinite boundary cases do not inherit a finite-depth conclusion.

### 11.3 Error price for the polynomial lower bound

Let `A_hat` be a real self-adjoint approximation with a **proved** error `||A_hat-A|| <= eta`. Do not clip or rescale it, even if an approximate eigenvalue is outside `[-1,1]`. For fixed exact `u,gamma`, telescoping powers gives
\[
 \boxed{|c_d(A,u)-c_d(A_{\rm hat},u)|
 \le\frac{\eta}{2}\|u\|^2
          \sum_{j=1}^{d}j(1+\eta/2)^{j-1}.}              \tag{46}
\]
**Proof.** Each exact `H_±` has norm at most one, each approximate one at most `1+eta/2`, and their difference has norm at most `eta/2`. The identity
`R^j-S^j = sum_{k=0}^{j-1} R^k(R-S)S^(j-1-k)`
bounds each power difference. Apply the quadratic-form bound separately to `X,Y` and use `||X||^2+||Y||^2=||u||^2`. QED. [ABSTRACT][PAPER]

If `||u-u_hat||<=epsilon_u`, an additional bound, using the exact operator first, is
\[
 (d+1)(2\|u_{\rm hat}\|\epsilon_u+\epsilon_u^2).
 \tag{47}
\]
Then apply (46) with `u_hat`. Enclose the phase through (43), and retain the scalar, normalization, quadrature and frequency-tail errors from §7.3. These estimates have no semilocal angle-gap denominator. They do not claim uniform efficiency when the polynomial degree increases, and an empirical `J` difference is not the proved `eta` used here.

This explains why the source overshoot is not fixed by dropping modes: a polynomial approximation can be used with its **full error price**, whereas an unpriced spectral deletion has no source order. For a lower certificate one can simply set `d=0` initially, which removes the approximate operator from the correction and keeps only the Mellin-vector norm. The pure scalar certificate corresponds to omitting all correction levels.

### 11.4 A source-free false-inference check, and the remaining source sign

Peak alignment alone is insufficient even after exact periodization. Consider the auxiliary multiplier `ell_test(xi)=exp(-xi^2)>0`. For every nonzero admissible compact smooth `h`,
`-int W_h ell_test < 0`, although the phase marginal is exactly the one in (10) and the weight still vanishes at the Euler harmonic lattice. This is a direct counterexample to inferring a floor sign from the marginal and the lobe zeros alone. It is **not** a counterexample for the literal `ell_2`.

The first source-specific inequality remains (9), or the weaker sufficient condition
\[
 F_{d,X}(h)\ge0
\]
with certified errors and the same test. If the scalar floor is negative, (42) shows precisely what must compensate it. No scalar-sign conclusion for the whole class or an unconditional positive infinite-dimensional subclass is added by this pass.

The reported tail replacement beyond 600 is one-sided only when it omits the exact nonnegative correction. It could support a **lower** result after all remaining source errors are certified. It cannot support a two-sided error bar or a planted **upper** result. `prod_op.py` changes the retained eigenmodes, while `prod_t.py` sets a previously unspecified constant to one; these are concrete reasons the supplied full margins do not yet satisfy that qualification.

### 11.5 Scoring, next action and verification boundary

The observer's eight probabilities and their base-verdict scores are preserved. This pass confirms the PAPER floor identity and source-specific stable representation; it does not upgrade either missing scalar-class event or the numerical margins. The compound prediction of two zero infima remains refuted by the exact shift. The prior PHASEPROOF positive-margin event remains unresolved at its complete-enclosure threshold. The four RESONANCE source/algebra results retain their paper status, not certification by observed slopes.

The base verdict's prospective checks are now assessed by this second reading as follows: `P_SF_SQUARE_AND_PACKET_IDENTITY_SURVIVES` (0.97), `P_SF_BSTAR_GAP_AND_GRAM_TRANSFER_SURVIVES` (0.90), and `P_SF_EXPLICIT_J_MAJORANT_SURVIVES` (0.91) pass this **paper recheck** with their stated domains and constants. This is not a Lean/interval gate and is not labelled a blinded third-party review. `P_SF_H4_SCALAR_CERTIFICATE_POSITIVE` (0.75) remains pending: no such run occurred.

New prospective registration: `P_SF_POLYNOMIAL_LOWER_HIERARCHY_SURVIVES`, probability **0.97**, event: a subsequent independent reviewer accepts (40)--(47) with the same source and error direction. Fate: **PENDING**. It predicts acceptance of this new derivation, not that the scalar sign is true.

The existing single next-task directive in §9 stays in force: certify the inverse-free scalar floor for the exact `h_4` profile with all errors. The hierarchy is an optional weaker representation for a later bounded transaction, not a replacement that silently rescores the pure-scalar forecast. No new numerical execution, Lean task, queue entry, or route promotion is authorized here.

**Consumer-first boundary.** The hierarchy is `NOT_NECESSARY` for the global Weil consumer. It reaches a specific test, or a declared finite packet, only through a genuine lower endpoint. The whole-class sign and the global all-test extension remain `RESEARCH_DEBT`; reopen them with a source inequality or certified counterexample, not with additional favourable rows. The additive proof result is the monotone hierarchy and its gap-free finite-degree error bound. It does not close an analytic RH supplier.

**Publication handoff.** Append this section to the existing expected verdict path on `rh_clean`, leaving its old bytes and predictions unchanged. Confirm a one-file, zero-deletion diff and read back the new blob. The receipt changes publication status only. No Lean axiom profile or kernel success is claimed.
