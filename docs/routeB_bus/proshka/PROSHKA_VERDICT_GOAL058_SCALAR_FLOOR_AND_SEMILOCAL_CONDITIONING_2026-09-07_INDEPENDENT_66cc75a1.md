# STATUS: TRY_SCALAR_FLOOR_WITH_SOURCE_GRAM_STABILIZATION
```yaml
OPERATIVE_CLASS: TRY_SCALAR_FLOOR_WITH_SOURCE_GRAM_STABILIZATION
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
  Q4: PARTIAL_WITH_PRECISE_REMAINDER
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
  FETCHED_USING_GITHUB_CONNECTOR: true
  FETCHED_UTF8_REENCODED_AND_HASHED: true
  SHA256_INDEPENDENTLY_RECOMPUTED: true
  GIT_OBJECT_SHA1_INDEPENDENTLY_RECOMPUTED: true
  BOTH_COUNTS_RECOMPUTED: true
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
CLOSES: [REQ-2026-09-07-SCALARFLOOR]
CLOSES_ANALYTIC_RH_SUPPLIERS: []
CLOSED_REVIEW_OBLIGATIONS:
  - real_contraction_scalar_floor_and_unnormalized_packet_order
  - explicit_scalar_Mellin_tail_majorants_without_fitted_constants
  - fixed_finite_Euler_source_angle_defect_comparison
  - pointwise_Sonin_image_Gram_representation_and_full_residual_bounds
  - false_factor_infimum_translation_and_testwise_detection_threshold
OPENS: []
DECISIONS:
  FLOOR_COMPARISON: PROVED_UNDER_EXACT_IDENTITY_6
  EXTRA_FLOOR_GE_NORM_U_SQUARED: PROVED
  NORMALIZED_MARGIN_IS_A_HERMITIAN_FORM: false
  UNNORMALIZED_MARGIN_IS_A_HERMITIAN_FORM: true
  FLOOR_NONNEGATIVE_ON_WHOLE_REQUEST_CLASS: NOT_PROVED
  FLOOR_NONNEGATIVE_ON_AN_EXPLICIT_INFINITE_DIMENSIONAL_SUBCLASS: NOT_PROVED
  SOURCE_COUNTEREXAMPLE_TO_THE_SCALAR_CLASS_CONDITION: NOT_PRODUCED
  H4_NUMERICAL_POSITIVITY_CERTIFICATE: NOT_ESTABLISHED
  REPORTED_DECIMATIONS_OR_J_SPREAD_ARE_RIGOROUS_ERROR_BOUNDS: false
  FIXED_S_TRUE_EIGENVALUES_CAN_CONVERGE_TO_PLUS_OR_MINUS_ONE_AS_J_INCREASES: false
  EXACT_NUMBER_OF_NEAR_UNIT_SOURCE_ANGLES: UNRESOLVED
  ONE_ADDITIONAL_NEAR_UNIT_ANGLE_PER_PRIME: NOT_ESTABLISHED
  STABLE_REPRESENTATION:
    type: ARCHIMEDEAN_SONIN_IMAGE_GRAM
    inverse_lower_bound: product_over_p_of_(1-p^(-1/2))^2
    involves_semilocal_1_minus_alpha_squared_in_error_constant: false
    remaining_input: certified_archimedean_evaluation_and_full_Galerkin_residual
  TRUE_K2_NONNEGATIVE: true
  TRUE_D2_SIGN_ON_ENTIRE_5_TO_16_INTERVAL: UNRESOLVED
  TRUE_D2_AT_2PI_OVER_LOG2: STRICTLY_POSITIVE_BY_PAPER_BOUND
  ZERO_LOW_FREQUENCY_INFLUENCE: false
  PLANTED_INFIMUM_EQUALS_TRUE_INFIMUM_MINUS_DELTA_M: true
  BOTH_INFIMA_EQUAL_ZERO: false
  TESTWISE_PLANT_OUTCOMES_FROM_REPORTED_DECIMALS: UNVERIFIED
EVIDENCE:
  NEW_MATHEMATICS_SCOPE: ABSTRACT
  NEW_MATHEMATICS_VERIFIER: PAPER
  SOURCE_INSTANTIATION_OF_FLOOR: CONDITIONAL_ON_RESONANCE_6_AND_ITS_DOMAINS
  NUMERICAL_ROWS_SCOPE: FINITE_CELL
  NUMERICAL_ROWS_VERIFIER: CONDITIONAL
  NUMERICAL_ROWS_STATUS: DIAGNOSTIC_NOT_ARB_INTERVAL
  INDEPENDENT_CHECK_12_EXCLUSIONS_RETAINED: true
  ALL_SHELF_SHA256_PREFIXES_RECOMPUTED: false
  POST_REQUEST_RESEARCH_USED: false
  HISTORICAL_PRIORITY_CLAIM: false
REVIEW_BOUNDARY: PAPER_PROOF_CONSTRUCTION_AND_ADVERSARIAL_REVIEW
AUTHORIZED_WRITE_SCOPE: VERDICT_DOC_ONLY
EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SCALAR_FLOOR_AND_SEMILOCAL_CONDITIONING_2026-09-07.md
PUBLICATION:
  ACTUAL_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SCALAR_FLOOR_AND_SEMILOCAL_CONDITIONING_2026-09-07_INDEPENDENT_66cc75a1.md
  EXPECTED_PATH_CREATION_ATTEMPT: REJECTED_422_CONCURRENT_FILE_CREATION
  CONCURRENT_VERDICT_COMMIT: 7333a9abf90954ae7c81c4849769ba8254560550
  CONCURRENT_VERDICT_BLOB: 9a96b510e7b35e30ffea982b4f14497b6d82584c
  CONCURRENT_VERDICT_OVERWRITTEN: false
  REASON_FOR_SEPARATE_ARTIFACT: CLOSED_GOAL_IMMUTABLE_PRESERVE_BOTH_INDEPENDENT_REVIEWS
  INDEPENDENT_DRAFT_BEFORE_COLLISION_SHA256: 3d061f91f7b2896a42b030a543283eab220e4de26012c8fdafd7b473cee44c41
  CONCURRENT_REVIEW_USED_AS_MATHEMATICAL_INPUT: false
HASH_COMPUTATION_PERFORMED: true
NUMERICAL_RUN_PERFORMED: false
SYMBOLIC_EXPERIMENT_RUN: false
LEAN_EDIT_PERFORMED: false
LEAN_KERNEL_RERUN: false
ARISTOTLE_SUBMISSION: false
QUEUE_OR_SHARED_STATE_EDIT: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## 0. Decision, evidence, and conventions

**The floor lemma is valid, and stronger than stated. The supplied decimals are not yet certificates. The semilocal conditioning can be removed from the inverse in an exact alternative representation, without changing the source. The sign of the scalar functional on the whole pole-null class is not established in this adjudication.**

The following are distinct: a theorem comparing two exact quantities; a numerical approximation to either quantity; an enclosure of the true quantity; and a universal sign theorem. This verdict supplies the first and explicit specifications for the third. It does not promote the second to the fourth. No numerical script was run. All new derivations are **[ABSTRACT][PAPER]**, subject to independent review; source statements using RESONANCE (6) retain its analytic identification/domain obligations. No Lean proof is claimed.

### Pinned sources

All repository sources below are read at the request commit, not at a moving research head.

- **[R]** `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_RESERVOIR_RESONANCE_AND_PRIME_SCALING_2026-09-06.md`, blob `ce20e425edcdaad189902e90c6b3dbe414b5bb34`: (1)--(18), (20)--(23), (25)--(27), (36).
- **[IC]** `docs/routeB_bus/RESONANCE_INDEPENDENT_CHECK_2026-09-06.md`, blob `06bbd3a2bdaae6c662c5b9de56e148a8008620bc`: algebraic checks, and especially its explicit exclusions in section 12. Its phrase “all eleven CORRECT” does not certify the trace-domain passage, numerical norm gap, or universal constants that section 12 excludes.
- **[ER]** `docs/routeB_bus/D2_SOURCE_EXACT_EVALUATOR_REPORT_2026-09-06.md`: reported numerical results and error diagnosis. These are evidence about the implementation, not rigorous enclosures.
- **[PG]** `docs/routeB_bus/phase5_codex/mellin_d2/PROGRESS.md`, blob `c717a1de9a3ad8fb751ce44b3738985da4564a7d`: the 02:40 follow-up explicitly says that the operator correction beyond 600 is omitted.
- **[CODE]** files in that directory: `core.py` (`73e6f3ce5c9d1799280a0e35670ef5b9c7fc1693`), `dens.py` (`bb924dee8e1df889324654d0d3b39516f5f5cd39`), `evald.py` (`e6e0c0754fbe0cac6feac3802cab492a193794ad`), `prod_op.py` (`dd7b88003c2a087419248205a2f5f531c239191b`), `s5b.py` (`cb26adaa446cea370df1c47d3f905330c2e4a03d`), `final.py` (`fcb8cd0d4e8c06c52cb4b34a00592569a17a76eb`). They were inspected, not executed.
- **[PP2]** `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_PHASE_CLASS_INEQUALITY_AND_MOLLIFIER_CROSSWALK_2026-09-06_UPLOADED_VERSION.md`, blob `9884019c5ed76f67225c9777a1cd91f115707ef5`: Lemma 5, full residual, and the strict open-support warning in B4. This request explicitly admits this second version.
- **[CCM23]** arXiv:2310.18423v2, sections 4.6--4.8, especially (58)--(59), Theorem 4.6, and (60): finite-Euler Sonin transport and the entire Mellin realization. **[CC20]** arXiv:2006.13771v1 is the archimedean background; no new global result is imported from it. **[C26]** arXiv:2602.04022v1 was consulted for the semilocal background, not as a supplier of the missing scalar sign. No new premise from math/9811068v1 is needed. **[DLMF]** 5.7.6 and 5.4(ii) supply the standard digamma identities used in section 5.3.

The request itself was reconstructed from the fetched UTF-8 content and hashed in the local runtime. Both hashes, 14243 bytes, 111 lines, and final LF match. The shelf prefixes are recorded by the request; they are not all claimed independently recomputed. Older uploaded project discussions are not substituted for these pinned sources.

Write \(a=\log2\), \(r=2^{-1/2}\), \(I=(-\delta_0,\delta_0)\), and
\[
 \mathcal H_{00}(I)=\{h\in C_c^\infty(I;\mathbb C):
        \int h(x)e^{x/2}dx=\int h(x)e^{-x/2}dx=0\}.
\]
Use \(\widehat h(\xi)=\int h(x)e^{-i\xi x}dx\), \(H=\|h\|_2^2\),
\[
 w_a(\xi)=1-\cos(a\xi),\qquad W_h=w_a|\widehat h|^2/H.
\]
For nonzero tests with support diameter less than \(a\), \(\int W_h=2\pi\), by the exact support/phase identity [R, (20)]. Set
\[
 \ell_S=2\Re(\gamma_St_S),\qquad
 F(h)=-\int W_h\ell_2,\qquad
 \mathfrak m(h)=-\int W_hd_2.
 \tag{1}
\]
The last identity is [R, (21)], with the fixed minus-lobe normalization. The scalar sufficient condition is **\(F(h)\ge0\)**, equivalently **\(\int W_h\ell_2\le0\)**.

## 1. Q1(a): exact floor, strengthened remainder, and packet order

### Theorem 1: real-contraction floor

Let a complex Hilbert space have conjugation \(J\). Suppose \(A=A^*\), \(AJ=JA\), \(\|A\|\le\alpha<1\), \(|\gamma|=1\), \(u\) belongs to the Hilbert space, and the source identity is
\[
 d=\ell+2\Re\{\gamma\langle u,A(I-A^2)^{-1}Ju\rangle\}
               -2\langle u,(I-A^2)^{-1}u\rangle,
 \quad\ell=2\Re(\gamma t).
 \tag{2}
\]
Inner products are conjugate-linear in the first argument. Then
\[
 \boxed{\ell-\frac{2}{1-\alpha}\|u\|^2
       \le d\le\ell-\frac{2}{1+\alpha}\|u\|^2
       \le\ell-\|u\|^2\le\ell.}
 \tag{3}
\]

**Proof.** Choose \(\gamma=e^{i\varphi}\) and write
\(e^{-i\varphi/2}u=x+iy\), where \(Jx=x\), \(Jy=y\). Reality and self-adjointness give the exact identity
\[
 R:=\ell-d
 =2\langle x,(I+A)^{-1}x\rangle
  +2\langle y,(I-A)^{-1}y\rangle.
 \tag{4}
\]
For example, substitute into (2) and use
\((I\mp A)(I-A^2)^{-1}=(I\pm A)^{-1}\); the real cross terms cancel. Both inverses have spectrum in \([1/(1+\alpha),1/(1-\alpha)]\). Also \(\|x\|^2+\|y\|^2=\|u\|^2\). This proves (3). The choice of square root of \(\gamma\) changes both real vectors by a sign and does not change any quantity. QED. **[ABSTRACT][PAPER]**

In a real eigenbasis, the exact mode is
\[
 d-\ell=-\sum_n\left(\frac{2x_n^2}{1+\lambda_n}
                         +\frac{2y_n^2}{1-\lambda_n}\right).
 \tag{5}
\]
This proves the observer's sign, including negative eigenvalues. With \(z_n=\langle\psi_n,u\rangle\), each mode before rotating its phase is
\(2[\lambda_n\Re(\gamma\bar z_n^2)-|z_n|^2]/(1-\lambda_n^2)\).
If \(z_n=\lambda_nc_n\), this is the formula in the request.

**Convergence repair.** The hypothesis \(\sum\lambda_n^2|c_n|^2<\infty\) suffices for the quadratic correction, since its absolute sum is bounded by \(2\|u\|^2/(1-\alpha)\). It does **not** justify \(t=\sum\lambda_n\bar c_n^2\). For example \(\lambda_n=1/(n+1)\), \(c_n=1\) has a finite weighted-square sum but a divergent first-order sum. Keep \(t_S\) defined by the Mellin integrals and retain the analytic justification of (6); do not reintroduce an unjustified expansion of the non-\(L^2\) Mellin wave. Compactness or an eigenbasis is not needed for the operator proof (4).

For a source density defined first almost everywhere, (3) holds almost everywhere. It holds at every real \(\xi\) once the continuous representatives asserted in [R] have been established. These are analytic obligations, not consequences of a random-matrix check to twelve digits. **[ABSTRACT][CONDITIONAL on source identification]**

### Corollary 1: the true packet statement is unnormalized

For a fixed packet \(h_1,\ldots,h_d\), define
\[
 \mathbf M_{ij}=-\int w_a\overline{\widehat h_i}\widehat h_j d_2,
 \qquad
 \mathbf F_{ij}=-\int w_a\overline{\widehat h_i}\widehat h_j\ell_2,
 \qquad \mathbf H_{ij}=\langle h_i,h_j\rangle.
\]
Then
\[
 \boxed{\mathbf M-\mathbf F\succeq0,\qquad
 \mathfrak m(\textstyle\sum c_jh_j)=\frac{c^*\mathbf Mc}{c^*\mathbf Hc}.}
 \tag{6}
\]
Indeed \(c^*(\mathbf M-\mathbf F)c=\int w_a|\sum c_j\widehat h_j|^2R_2\ge0\). Integrability follows from the source bounds and smooth tests. The normalized margin itself is a homogeneous quotient, **not** a Hermitian quadratic form. A Gram matrix and all mixed entries are required for packet certification. Positive diagonal sample values are insufficient: \(\left(\begin{smallmatrix}1&2\\2&1\end{smallmatrix}\right)\) is an exact counterexample to that inference. **[FINITE_CELL][PAPER]**

## 2. Q1(b): what the scalar condition proves, and what remains unproved

For the true source, Theorem 1 proves
\[
 \boxed{\mathfrak m(h)\ge F(h)+\frac{2}{1+\alpha_2}
           \int W_h\|u_2\|^2\ge F(h).}
 \tag{7}
\]
It does not prove \(F(h)\ge0\). A negative scalar floor refutes that sufficient certificate on that test, not the source inequality. Conversely a certified nonnegative floor proves the source inequality without computing the inverse.

### 2.1 Why the proposed resonance argument does not determine the sign

The exact marginal is
\[
 \sum_{k\in\mathbb Z}\left|\widehat h((\theta+2\pi k)/a)\right|^2=aH.
 \tag{8}
\]
It controls a periodic function of \(a\xi\). The scalar \(\ell_2(\xi)\) includes the archimedean gamma phase and the incomplete Mellin integrals; it is not specified by a positive Poisson kernel of the phase alone. In particular [R]'s decay of \(t_2\) is incompatible with calling its modulus a fixed nonzero periodic function. An envelope with varying amplitude is a different assertion, also needing a proof. Differentiating a geometric Mellin sum can introduce a squared denominator; it does not preserve a guessed Poisson law.

Even exact coincidence of modulus peaks with zeros of \(w_a\) would not determine the sign of \(\Re(\gamma_2t_2)\). As a falsifier of that *inference*, take the smooth real symbol
\(\ell(\xi)=e^{-\xi^2}(1+\cos(a\xi))\). It peaks at phase zero but
\(-\int W_h\ell<0\) for every nonzero compact test: the integrand is positive except on discrete sets. This is not asserted to be the source symbol. It refutes the proposed peak-placement implication, not (R-SIGN). **[ABSTRACT][PAPER]**

The incomplete-gamma formula in the request, with consistent branches, is a legitimate exact representation. Equivalently, for fixed \(\beta\) and \(s=1/2-i\xi\),
\[
 J(\beta,-\xi)=\sum_{n\ge0}\frac{(-1)^n\beta^{2n}}{(2n)!(s+2n)^2}.
 \tag{9}
\]
Absolute convergence permits integration term by term for this one integral. It does not permit interchanging this Taylor series with the infinite Euler-dilation sum: the \(n=0\) coefficient of the latter already diverges. Nor is exact closed form synonymous with exact floating-point evaluation.

### 2.2 The exact remaining scalar operator

Let \(E_I:L^2(I)\to L^2(\mathbb R)\) be zero extension, \(\mathcal F\) the unitary Fourier transform, and \(\Pi_{00}\) the orthogonal projection off the span of \(e^{x/2},e^{-x/2}\) in \(L^2(I)\). The source bounds give a real bounded symbol \(w_a\ell_2\) tending to zero at infinity. Thus
\[
 K_F=-2\pi\Pi_{00}E_I^*\mathcal F^*M_{w_a\ell_2}\mathcal F E_I\Pi_{00}
 \tag{10}
\]
is a compact self-adjoint operator and
\(F(h)=\langle h,K_Fh\rangle/\|h\|^2\) on the pole-null class.

**Proof of compactness.** Restrict the multiplier to \([-R,R]\). Its kernel on the finite interval is bounded and square-integrable, hence gives a compact operator. The operator norm of the omitted multiplier is at most \(2\pi\sup_{|\xi|>R}|w_a\ell_2|\to0\). The pole-null smooth class is dense in the corresponding closed two-moment-null space: approximate in \(L^2\), then correct the two moments with two fixed interior smooth bumps with independent moment vectors. QED. **[ABSTRACT][PAPER]**

The first unproved inequality is precisely
\[
 \boxed{\langle h,K_Fh\rangle\ge0
       \quad\text{for all }h\in\operatorname{ran}\Pi_{00}.}
 \tag{SF-CLASS}
\]
No source counterexample to it is produced here. No independently defined infinite-dimensional subclass with its sign proved is supplied. Defining a subclass by \(F(h)\ge0\) would not answer the question. Exact Fourier-band localization is unavailable for a nonzero compactly supported test. The pole-null high-modulation family from [R] gives \(F(h_T)\to0\), but a limit of zero has no sign, and separate modulations do not certify their arbitrary linear combinations.

Two legitimate representations remain: (10), retaining the exact scalar kernel and its pole-null compression; and the positive-correction hierarchy below, which need not satisfy the stronger scalar condition. The original consumer requires \(\mathfrak m\ge0\), not (SF-CLASS).

### 2.3 Positive-correction hierarchy, without inverse evaluation

Put \(T_x=(I-A_2)/2\), \(T_y=(I+A_2)/2\), and \(\rho=(1+\alpha_2)/2<1\). Both operators are positive contractions. By a geometric-series identity,
\[
 R_2(\xi)=\sum_{n\ge0}\bigl(\langle x,T_x^nx\rangle+
                                      \langle y,T_y^ny\rangle\bigr).
\]
Consequently
\[
 \mathfrak m(h)=F(h)+\sum_{n\ge0}C_n(h),\quad
 C_n(h)=\int W_h(\langle x,T_x^nx\rangle+\langle y,T_y^ny\rangle)\ge0.
 \tag{11}
\]
Tonelli applies to this positive part. Every partial sum is a lower bound. Its tail is bounded by
\(\rho^{N+1}(1-\rho)^{-1}\int W_h\|u_2\|^2\). This is a theorem about the exact operator, not permission to use an out-of-contraction discretization. It can converge slowly when \(\alpha_2\) is close to one. For a fixed strictly positive true margin, some exact finite partial sum is positive; for a zero margin no finite certificate is promised. **[ABSTRACT][PAPER]**

## 3. Q1(c): two-sided bounds and explicit scalar integration budgets

### 3.1 Matching comparison

With \(U(h)=\int W_h\|u_2\|^2\), (3) gives
\[
 \boxed{F(h)+\frac{2}{1+\alpha_2}U(h)
       \le\mathfrak m(h)\le F(h)+\frac{2}{1-\alpha_2}U(h).}
 \tag{12}
\]
The scalar \(\|u_2(\xi)\|^2\) can be computed from the direct Mellin integrals (10) of [R]; no inverse is used in it. The upper constant still needs a strict norm bound. Section 4 supplies one from archimedean data, and section 5 gives another pair of scalar envelopes that avoids a semilocal near-unit denominator altogether.

There is no generic two-sided bound depending on \(t\) alone. In the finite real model \(A=I/2\) on \(\mathbb C^2\), take \(f=(s,is)\), \(u=Af\), \(\gamma=1\). Then \(t=\langle f,A\bar f\rangle=0\) for all real \(s\), while (2) gives \(d=-4s^2/3\). This rules out such a generic bound without correction data. It is not a counterexample to a new, source-specific identity one might prove. **[ABSTRACT][PAPER]**

### 3.2 A fully explicit, deliberately conservative Mellin tail

The following bound replaces an unspecified or empirically fitted constant. For \(\beta\ge1\), \(T\ge|\xi|\), put \(s_T=\sqrt{1/4+T^2}\). Then
\[
 \boxed{|J(\beta,\xi)|\le\beta^{-1/2}
                   [6+(3+2s_T)\log\beta].}
 \tag{13}
\]
**Proof.** Split the integral at \(1/\beta\). The absolute integral on the first part is \(\beta^{-1/2}(2\log\beta+4)\). On the second part integrate the cosine once. The boundary costs \(\beta^{-1/2}\log\beta\); the derivative satisfies
\[
 |[(-\log v)v^{-1/2+i\xi}]'|
 \le v^{-3/2}[1+s_T(-\log v)].
\]
Its integrals are bounded by \(2\sqrt\beta\) and \(2\sqrt\beta\log\beta\), respectively. Division by \(\beta\) proves (13). QED. **[ABSTRACT][PAPER]**

For the one-prime scalar in this request,
\[
 t_2(\xi)=\frac1{2\pi}\left[\sum_{j\ge0}J(2\pi2^j,-\xi)-J(\pi,-\xi)\right].
\]
Writing \(\beta_j=2\pi2^j\), the truncation after \(j=J\) has the uniform error on \(|\xi|\le T\)
\[
 \boxed{\varepsilon_t(J,T)=\frac{r^{J+1}}{2\pi\sqrt{2\pi}}
 \left[\frac{6+(3+2s_T)\log\beta_{J+1}}{1-r}
       +\frac{(3+2s_T)ar}{(1-r)^2}\right].}
 \tag{14}
\]
This follows by summing a geometric series and its first moment. It is not claimed sharp, and it does not retroactively certify the report's \(3.5\cdot10^{-8}\). Increasing the scalar Euler cutoff does not require increasing the Nyström carrier.

There is also a global elementary envelope. Define
\[
 K_0=\frac1{2\pi}\left[\frac{6+4\log\pi}{\sqrt\pi}
 +\frac1{\sqrt{2\pi}}\left(
 \frac{6+4\log(2\pi)}{1-r}+\frac{4ar}{(1-r)^2}\right)\right],
\]
\[
 K_1=\frac1{2\pi}\left[\frac{2\log\pi}{\sqrt\pi}
 +\frac1{\sqrt{2\pi}}\left(
 \frac{2\log(2\pi)}{1-r}+\frac{2ar}{(1-r)^2}\right)\right].
\]
Since \(s_T\le T+1/2\), (13) yields
\[
 |t_2(\xi)|\le K_0+K_1|\xi|.
 \tag{15}
\]
This bound is weaker than [R]'s asymptotic decay but has explicit constants and is adequate for smooth-test tail certification. If integration by parts is valid to order \(q\ge2\), with \(D_q\ge\|h^{(q)}\|_1\), then
\[
 \boxed{\left|\int_{|\xi|>T}W_h\ell_2\right|
 \le\frac{8D_q^2}{H}
 \left(\frac{K_0T^{1-2q}}{2q-1}
             +\frac{K_1T^{2-2q}}{2q-2}\right).}
 \tag{16}
\]
Indeed \(|\widehat h|\le D_q|\xi|^{-q}\), \(w_a\le2\), and \(|\ell_2|\le2(K_0+K_1|\xi|)\); integrate both half-lines. This is an explicit tail proof, not a “mass deficit times the last grid maximum” heuristic. A sharper analytic transform bound may replace it after proof.

### 3.3 What an actual scalar certificate must enclose

For a chosen fixed test, enclose the **unnormalized** integral \(N_F=-\int w_a|\widehat h|^2\ell_2\) and \(H>0\). Budget separately: finite-frequency quadrature, evaluation of \(J\) and its parameter derivative, the gamma phase and branches, Fourier transform of the test, normalization, Euler tail (14), and frequency tail (16). For example, if \(|t-\widetilde t|\le\epsilon_t\) and \(|\gamma-\widetilde\gamma|\le\epsilon_\gamma\), then
\[
 |\ell-2\Re(\widetilde\gamma\widetilde t)|
 \le2(\epsilon_t+\epsilon_\gamma|\widetilde t|).
 \tag{17}
\]
A uniform error \(\epsilon\) in \(t\), with the phase exact, costs at most \(4\pi\epsilon\) in the normalized floor, using \(\int W_h=2\pi\).

An exact incomplete-gamma formula is not an enclosure of its evaluation. `mpmath.diff`, conversion to ordinary complex numbers, a fixed precision, and agreement with a second formula do not by themselves bound roundoff or truncation. The code uses these operations; it does not implement the complete above certificate. The report's table of observed constants is not a proof of those constants. **[FINITE_CELL][CONDITIONAL for the proposed certificate]**

## 4. Q2(a): the exact source excludes unit limiting angles at fixed S

### Theorem 2: transfer of the angle defect

This is a new paper derivation from the source intertwining; it is not inferred from the reported eigenvalues. Work on the log line, with \(P=1_{(-\infty,0]}\), \(Q=I-P\). For a fixed finite prime set let
\[
 B=\prod_{p\in S\setminus\{\infty\}}(I-r_pU_{a_p}),\quad
 b_-=\prod_p(1-r_p),\quad b_+=\prod_p(1+r_p),\quad \kappa=b_+/b_-.
\]
Then \(B,B^{-1},B^*,(B^*)^{-1}\) are bounded; \(B^*\) and its inverse preserve \(P\mathcal H\). The exact Fourier involutions satisfy
\[
 F_S=(B^*)^{-1}F_\infty B^*,\qquad F_\infty B^*=B^*F_S.
\]
Put \(A_S=PF_SP|_{P\mathcal H}\), \(A_\infty=PF_\infty P|_{P\mathcal H}\),
\(D=PB^*P|_{P\mathcal H}\), and \(C=QB^*Q|_{Q\mathcal H}\). The latter two operators are invertible and have norm at most \(b_+\), inverse norm at most \(b_-^{-1}\). Block triangularity proves the inverse assertion for \(C\); it is not an arbitrary compression/inverse interchange.

For the leakage maps \(T_S=QF_SP\), \(T_\infty=QF_\infty P\), the intertwining gives
\(T_\infty D=CT_S\). Therefore
\[
 \boxed{b_+^{-2}D^*(I-A_\infty^2)D
       \preceq I-A_S^2
       \preceq b_-^{-2}D^*(I-A_\infty^2)D.}
 \tag{18}
\]
Here \(T_S^*T_S=I-A_S^2\) uses the **true unitary involution**. In particular
\[
 \boxed{I-A_S^2\succeq
       \kappa^{-2}(1-\|A_\infty\|^2)I>0.}
 \tag{19}
\]
The archimedean strict inequality follows because its compression is compact and a common compact-support Fourier vector must be zero. Norm attainment otherwise gives such a vector. This proves (19) without any numerical approximation to the semilocal top angles. QED. **[ABSTRACT][PAPER]**

For one prime 2, \(\kappa^2=17+12\sqrt2\). A *certified* archimedean bound \(\|A_\infty\|\le\bar\alpha_\infty<1\) would give
\[
 1-\|A_2\|^2\ge
 (1-\bar\alpha_\infty^2)/(17+12\sqrt2).
 \tag{20}
\]
The decimal archimedean eigenvalue in the request is not used as a certified value here.

Thus at fixed cutoff and fixed finite \(S\), the true angles are fixed numbers strictly inside \((-1,1)\). Increasing \(J\) improves an approximation; it does not move the true operator toward a new endpoint operator. Once a genuine operator-norm approximation converges, its extremal eigenvalues cannot tend to exactly \(\pm1\). The geometric extrapolation to \(1.0024\) is incompatible with the source and is not a limiting-value theorem.

The exact number of eigenvalues *near* either endpoint depends on a declared threshold. It is not determined here. More quantitatively, the variational eigenlevels \(\mu_j\) of the positive defects satisfy
\[
 \kappa^{-2}\mu_j(I-A_\infty^2)
 \le\mu_j(I-A_S^2)\le\kappa^2\mu_j(I-A_\infty^2),
 \tag{21}
\]
by min--max and the invertible map \(D\), with its two norm bounds. This controls possible low-defect counts, not “one new angle per prime.” The finite-Euler map is not an isometry of the compressed problems, and need not send a single archimedean eigenvector to an eigenvector. Failure of a Hilbert--Schmidt property concerns summability of the tail of singular values, not the count at the opposite endpoint. No cardinality law in \(|S|\) or source values of the two alleged angles is proved by the shelf.

## 5. Q2(b)--(c): a stable source representation, diagnosis, and low-frequency signs

### 5.1 Sonin-image Gram coordinates

Let \(P_0\) project onto the **archimedean** Sonin space \(\mathcal H_0\). The source intertwining and one-sided support preservation imply
\(\mathcal H_S=B\mathcal H_0\), as in [CCM23] and [PP2]. Define
\[
 G=P_0B^*BP_0|_{\mathcal H_0},\qquad
 g_-=b_-^2,\quad g_+=b_+^2.
\]
Then
\[
 \boxed{g_-I\preceq G\preceq g_+I,\qquad
 \mathsf S_S=BP_0G^{-1}P_0B^*.}
 \tag{22}
\]
**Proof.** The bounds are the norm bounds of \(B\). The operator \(BP_0G^{-1/2}\) is an isometry onto \(B\mathcal H_0\), giving its orthogonal projection. Alternatively, \(F_SB=BF_\infty\) and support preservation for \(B,B^{-1}\) prove equality of the two Sonin spaces directly. QED. **[ABSTRACT][PAPER]**

For almost every \(\xi\), let \(w_\xi\in\mathcal H_0\) be the vector of archimedean Fourier evaluations, so \(\|w_\xi\|^2=k_\infty(\xi)\) and \(\langle w_\xi,f\rangle=\mathcal Ff(\xi)\) on the evaluation domain. It exists from the square-summable evaluation sequence used in [R]; the entire Mellin model gives the compatible pointwise realization. Write \(b(\xi)=\prod_p(1-r_pe^{-ia_p\xi})\). Then
\[
 \boxed{k_S(\xi)=|b(\xi)|^2\langle w_\xi,G^{-1}w_\xi\rangle,
       \qquad d_S=k_S-q_S/(2\pi).}
 \tag{23}
\]
This follows by applying Fourier evaluation to the isometry in (22). In particular
\[
 \boxed{\frac{|b|^2}{g_+}k_\infty-\frac{q_S}{2\pi}
       \le d_S\le
       \frac{|b|^2}{g_-}k_\infty-\frac{q_S}{2\pi}.}
 \tag{24}
\]
These are matching scalar envelopes involving the archimedean density and explicit Euler factors, not the unknown semilocal near-unit gap. They may be too crude for the final sign, but their direction is rigorous.

**Pointwise full-residual sandwich.** For any trial vector \(y\in\mathcal H_0\), put
\[
 r_\xi=w_\xi-Gy,\qquad
 J_\xi(y)=2\Re\langle w_\xi,y\rangle-\langle y,Gy\rangle.
\]
Completing the square gives
\[
 \boxed{J_\xi(y)+\frac{\|r_\xi\|^2}{g_+}
 \le\langle w_\xi,G^{-1}w_\xi\rangle
 \le J_\xi(y)+\frac{\|r_\xi\|^2}{g_-}.}
 \tag{25}
\]
For Galerkin \(y\) this is the pointwise counterpart of [PP2, Lemma 5]. The residual is full-space. Computing its norm needs \(FG^2F\), not \((FGF)^2\); the parent's exact \(n=4/3\) plant remains mandatory.

If \(\|\widetilde G-G\|\le\eta<g_-\) and \(\|\widetilde w-w\|\le\epsilon\), then
\[
 \left|\langle w,G^{-1}w\rangle-
 \langle\widetilde w,\widetilde G^{-1}\widetilde w\rangle\right|
 \le\frac{\epsilon(2\|\widetilde w\|+\epsilon)}{g_-}
 +\frac{\eta\|\widetilde w\|^2}{g_-(g_--\eta)}.
 \tag{26}
\]
Expand first in the vector, then use the resolvent identity. This is an error estimate **without a factor \((1-\alpha_S^2)^{-1}\)**. For one prime \(g_-=(1-1/\sqrt2)^2\) is explicit. It still requires error-controlled archimedean evaluation, construction of the carrier inside \(\mathcal H_0\), full residuals, and scalar evaluation of \(b,q_S\). It is not a claimed ready-made implementation. Its constants are not uniform in a growing prime set.

Merely writing (4), or shifting a resolvent, is not the same stabilization. A generic inverse near a small eigenvalue is sensitive: with \(A=1-\varepsilon\), \(\gamma=1\), \(\u=i\), the correction is \(2/\varepsilon\). Perturbing \(A\) by \(\eta<\varepsilon\) changes it by \(2\eta/[\varepsilon(\varepsilon-\eta)]\). This exact model rules out a gap-independent black-box error bound based on \(\|\widetilde A-A\|\) alone. It does not rule out (22)--(26), which use additional source structure. **[ABSTRACT][PAPER]**

### 5.2 What is demonstrably wrong in the evaluator

`prod_op.py` computes the eigenvectors of the truncated Nyström matrix, then applies
`keep = abs(lam) < 1 - 1e-12`. It discards the other modes. Its vector \(u\) is also obtained from that truncated kernel, while `dens.t_S` supplies a much longer scalar Euler sum. Thus the assembled row is **not** the exact identity (6) for the true operator, and is not even a source-unitary identity for the truncated Fourier multiplier.

This identifies a concrete invalid certification step, not necessarily the single dominant numerical contribution at \(\xi=8\). The negative value can involve the missing mode, the remaining quadratic terms, vector error, and arithmetic cancellation against \(q_S/(2\pi)\). The scalar \(t_S\) was independently evaluated; this does not certify the whole combination.

Discarding an **exact** source mode would raise \(d\) and lower \(\mathfrak m\), by (5). But approximate eigenvectors are not certified exact spectral subspaces. No one-sided source conclusion follows merely by discarding their out-of-range modes. Conversely, on the exact source, dropping all correction terms beyond 600 produces a lower approximation to \(\mathfrak m\), not an upper approximation. It cannot by itself establish that the false-factor margin is negative.

The multiplier tail \((1+r)r^{J+1}\) is a genuine norm bound for the uncompressed Euler truncation. It must be combined with quadrature and a valid inverse/geometry estimate. A spread between \(J=7\) and \(J=8\) is not a source-error bound. A small unweighted share \(|b_n|^2\) does not bound the weighted quantity \(|b_n|^2/(1-\lambda_n^2)\). Statements that small-frequency conditioning is “irrelevant” are therefore not established. **[FINITE_CELL][PAPER audit; numerical values CONDITIONAL]**

### 5.3 True signs: one rigorous positive point, not a grid classification

By (23), \(k_2\ge0\). Therefore the negative computed density is not a possible source feature. However, this does not mean \(d_2\ge0\): \(d_2=k_2-q_2/(2\pi)\). Two scalar sign gates are available:
\[
 \ell_2(\xi)<0\Longrightarrow d_2(\xi)<0,
 \qquad q_2(\xi)<0\Longrightarrow d_2(\xi)>0.
 \tag{27}
\]
The second implication is strict because \(k_2\ge0\).

Here is a fully analytic positive point inside the requested interval. Set \(\xi_*=2\pi/\log2\), \(y=\xi_*/2\). Then \(5<\xi_*<16\), \(y<5\), and
\[
 q_2(\xi_*)=q_\infty(\xi_*)-2(\log2)(\sqrt2+1).
\]
The digamma series [DLMF 5.7.6] gives, with \(x=1/4\),
\[
 \Re\psi(x+iy)=\psi(x)+
 \sum_{n\ge0}\frac{y^2}{(n+x)((n+x)^2+y^2)}
 <\psi(1/4)+4+\tfrac12\log(1+16y^2).
\]
For the terms \(n\ge1\), integrate the decreasing positive summand from \(x\) to infinity; its integral is the displayed logarithm. Use
\(\psi(1/4)=-\gamma_E-\pi/2-3\log2<-7/2\), \(y<5\), and
\(\sqrt{401}<21\), to obtain
\[
 q_\infty(\xi_*)<\tfrac12+\log(21/\pi)<\tfrac52.
\]
Finally \(\log2>2/3\), \(\sqrt2>7/5\), so the Euler subtraction is greater than \(16/5\). Hence
\[
 \boxed{q_2(\xi_*)<-7/10,\qquad d_2(\xi_*)>7/(20\pi)>0.}
 \tag{28}
\]
Continuity gives an open positive neighborhood. These intentionally loose rational bounds require no numerical run. They do not classify the entire interval \([5,16]\). No certified negative subinterval of the true source is inferred from the reported table here. **[ABSTRACT][PAPER]**

The report's “\(k_\infty=0\) exactly for \(\xi\le2\)” must not be imported as a theorem. If the sum of evaluation squares vanished on an interval, every Sonin Mellin transform would vanish there; the entire realization [CCM23, (60)] and the nonzero gamma factor on the line would make the nonzero space trivial. Small values below numerical resolution are different from an interval of exact zeros.

Likewise, for a low-frequency set \(E\), the valid sensitivity estimate is
\[
 |\Delta\mathfrak m_E|\le
 \left(\int_EW_h\right)\operatorname*{ess\,sup}_E|d_2-\widetilde d_2|.
 \tag{29}
\]
For a nonzero compact test, \(W_h\) is positive almost everywhere on an interval away from discrete zeros; its low-frequency mass is not exactly zero. A reported fraction of 0.05% is not exact insensitivity. Equation (24) offers a source-faithful way to bound the low-frequency error when the archimedean evaluations are enclosed.

## 6. Q3: exact plant logic and the limits of the reported margins

For the specified arithmetic-only false factor, keep the same Sonin projector and the same normalized class. The parent gives the exact constant
\[
 \delta_M=2a(\cosh(a/4)-1)>0,\qquad
 \boxed{\mathfrak m_\sharp(h)=\mathfrak m(h)-\delta_M.}
 \tag{30}
\]
Consequently, for the identical class \(\mathcal C\),
\[
 \boxed{\inf_{h\in\mathcal C}\mathfrak m_\sharp(h)
       =\inf_{h\in\mathcal C}\mathfrak m(h)-\delta_M.}
 \tag{31}
\]
Both infima are finite for the bounded source multiplier; the equality also holds in the extended sense. **They cannot both equal zero.** If the genuine whole-class inequality is eventually proved, [R]'s high-modulation family supplies \(\inf\mathfrak m=0\), and then \(\inf\mathfrak m_\sharp=-\delta_M\), not zero.

Without assuming the genuine sign, [R]'s explicit smooth pole-null family
\(h_T=(\partial^2-1/4)(\eta\cos Tx)\) and source decay give
\[
 \mathfrak m(h_T)\to0,\qquad
 \mathfrak m_\sharp(h_T)\to-\delta_M.
\]
Thus for all sufficiently large \(T\),
\[
 \boxed{\mathfrak m_\sharp(h_T)<-\delta_M/2<0.}
 \tag{32}
\]
This retains the parent's whole-class plant refutation, conditional on the same source-density and decay premises. It does not require a certification of the observer's frozen test. **[ABSTRACT][PAPER with the stated source dependencies]**

Testwise detection is exactly \(\mathfrak m(h)<\delta_M\); survival is \(\mathfrak m(h)\ge\delta_M\). Test-dependent survival is therefore expected for a constant shift. It is not, by itself, a uniqueness theorem identifying zeta among other arithmetic models.

For certified enclosures \([L_m,U_m]\) and \([L_\delta,U_\delta]\), the gates are:

| Conclusion | Required inequality |
|---|---|
| Genuine phase inequality on this test | \(L_m\ge0\) |
| False factor fails on this test | \(U_m<L_\delta\) |
| False factor survives on this test | \(L_m\ge U_\delta\) |
| Neither comparison resolves | INCONCLUSIVE; keep the signed interval |

A lower scalar floor alone cannot certify plant failure. The \(J\)-spread does not supply either endpoint. In particular, the omitted positive correction beyond 600 works against an asserted upper bound on the true \(\mathfrak m\). The margins 0.003--0.005 may be real, but their distance from a reported spread, even by a factor of ten, is not a proof.

### Admissibility repair for the test rows

The polynomial probes \(\eta_k=N_k(1-(x/\delta_0)^2)^k\), zero outside the window, are not compactly supported **smooth** functions on the open interval. For \(k=2\), \(h_k\) has endpoint jumps; for \(k=4\), it is \(C^1\) across the endpoints but is not \(C^\infty\). The flat frozen bump is smooth on the whole line but its support reaches \(\pm\delta_0\); [PP2, B4] already notes this open-interval distinction.

This is repairable, not a route obstruction. The zero extensions of \(\eta_2,\eta_4\) lie in \(H^2(\mathbb R)\); the function and its first derivative vanish at both endpoints. Shrink their support inward and mollify \(\eta_k\), obtaining \(\eta_{k,\epsilon}\in C_c^\infty(I)\) converging in \(H^2\). Then
\(h_{k,\epsilon}=(\partial^2-1/4)\eta_{k,\epsilon}\to h_k\) in \(L^2\), with both pole moments zero exactly. The same inward-cutoff approximation applies to the flat bump. Because \(w_ad_2\) and \(w_a\ell_2\) are bounded, the unnormalized margin and floor are continuous in \(L^2\). For unit vectors, a form with operator norm \(M\) changes by at most \(2M\|h-g\|\). Thus a **certified strictly positive** extended-test margin transfers to a specified sufficiently close admissible smooth test after paying this norm error. Mere diagnostic positivity cannot fund that transfer. **[ABSTRACT][PAPER]**

## 7. Q4: the smallest theorem and the exact certificate still missing

The unconditional abstract theorem now proved is Theorem 1 and its packet corollary. Its source specialization is:

> For every nonzero pole-null compact smooth test in the original short window, assuming the established source identification (6) with its analytic domains, the true margin is at least its explicit scalar floor, and at least the strengthened floor (7). Every exact finite packet has the matrix order (6).

It is **not** presently a theorem that the floor is nonnegative on the entire class. Nor do the supplied files prove \(\mathfrak m(h_4)\ge0.0035\). A reported floor \(0.003509\) would imply
\[
 \mathfrak m(h_4)\ge0.003509-E_F
 \tag{33}
\]
only after a rigorous bound \(E_F\) for *all* scalar and test errors, including any rounding of that reported center. Positivity needs \(E_F<0.003509\); the stronger lower value 0.0035 needs \(E_F\le9\cdot10^{-6}\), less the reporting-roundoff allowance. There is no such completed enclosure in the inspected files. Membership in the literal smooth open-interval class also requires the preceding repair.

The current implementations use floating-point Nyström matrices, dropped modes, ordinary special-function evaluation, and trapezoidal sums. In `s5b.py` and `final.py`, a maximum observed on \([500,600]\) is used as though it bounded the entire tail; that is not a valid implication. [PG] subsequently extends the scalar integral but explicitly retains only the leading term beyond 600. [IC, section 12] expressly leaves analytic trace regularization and numerical constants outside its check. None of these observations refutes the positive row. They do preclude the label **ARB_INTERVAL** and the phrase “rigorous floor +0.0020” at the current evidence cutoff.

The first complete certificate should return an enclosure of \(N_F\) and \(H\), including (14)--(17), on the frozen source-defined test or on a declared smooth approximation with its norm budget. If its lower endpoint is nonnegative, then \(L_2(v_h)\ge n_2(v_h)\ge0\) follows for that test. A packet certificate uses the entire matrix (6). Neither result is a global all-test Weil theorem, and no historical “first” claim is made.

## 8. Predictions, scoped findings, and next action

### 8.1 Frozen observer predictions

The original probabilities and events are retained. A delivery prediction can fail in this adjudication without refuting the mathematical conjecture.

| Prediction | p | Fate |
|---|---:|---|
| P_FLOOR_LEMMA_THEOREM | 0.85 | CONFIRMED, as a paper theorem under (6), with strengthened bounds and the convergence repair. |
| P_SCALAR_CONDITION_ON_CLASS | 0.30 | NOT ACHIEVED in this adjudication; the mathematical sign (SF-CLASS) remains UNRESOLVED, not refuted. |
| P_SCALAR_CONDITION_ON_SUBCLASS | 0.50 | NOT ACHIEVED; no non-tautological infinite-dimensional positive subclass is proved. A high-modulation limit of zero is insufficient. |
| P_TWO_UNIT_ANGLES_SOURCE_FEATURE | 0.65 | UNRESOLVED for a thresholded near-unit count and its growth. Exact convergence to unit endpoints at fixed S is REFUTED by (19); the report does not identify source limiting values. |
| P_STABLE_REPRESENTATION | 0.50 | CONFIRMED at the analytic representation level by (22)--(26). Certified archimedean evaluation/full residual data are still needed to implement it. |
| P_K2_NEGATIVE_IS_TRUNCATION | 0.80 | CONFIRMED that the true density is nonnegative and the observed negative row is not a source feature. Specific relative blame among implementation errors is not uniquely established. |
| P_PLANT_TEST_DEPENDENCE_EXPECTED | 0.60 | REFUTED AS THE COMPOUND EVENT: threshold-dependent survival is correct, but “inf = 0 for both” contradicts the exact translation (31). |
| P_SMALLEST_THEOREM_IS_FINITE_TEST | 0.70 | REFUTED AS THIS BATCH'S OUTPUT: the proved result is a universal comparison theorem; a numerical finite-test certificate is not yet established. |

### 8.2 Earlier judge registrations named by the request

| Earlier prediction | Original p | Fate retained in this review |
|---|---:|---|
| P_PHASEPROOF_SOURCE_PACKET_MINUS_MARGIN_POSITIVE | 0.70 | Positive diagnostics SUPPORT it. Source-certification status remains UNRESOLVED: no full lower enclosure has returned. Do not score a floating-point floor as a certified sign. |
| P_R_PERIODIZATION_SURVIVES | 0.99 | CONFIRMED on paper by support/autocorrelation uniqueness; the independent check supports it. |
| P_R_SOURCE_REMAINDER_DECAYS | 0.76 | Parent PAPER derivation retained, with independent algebra/exponent support and [IC, section 12] exclusions. Fitted exponents do not independently prove the source asymptotic or its constants. |
| P_R_PEAK_NOTCH_AND_POSITIVE_ATOM | 0.97 | CONFIRMED algebraically by the exact polynomial from [R]; not a statement about the full reservoir sign. |
| P_R_LOG_GAIN_FAILS | 0.94 | Parent paper counterexample retained with its fixed-prime/high-modulation dependency. No numerical ratio replaces its quantifier. |

No old probability or artifact is edited. The supplied eight-digit archimedean agreement and the carrier's failure at higher frequencies remain cross-checks, not interval-certified errors. An \(O(\xi^{-2})\) statement also does not imply the reported pointwise limit \(\xi^2d_\infty\to-7.3\); that stronger asymptotic has not been established here.

### 8.3 New prospective registrations

These are subjective forecasts **for future independent gates**, registered after reading the request and its diagnostics, not blind predictions preceding them:

```yaml
NEW_PREDICTIONS:
  P_SF_OPERATOR_FLOOR_REVIEW_SURVIVES:
    probability: 0.99
    event: independent_paper_or_kernel_check_accepts_Theorem_1_without_statement_change
    fate: PENDING
  P_SF_IMAGE_GRAM_STABILIZATION_SURVIVES:
    probability: 0.92
    event: independent_source_check_accepts_18_through_26_with_the_same_cutoffs
    fate: PENDING
  P_SF_FROZEN_FULL_SCALAR_CERT_POSITIVE:
    probability: 0.70
    event: full_error_lower_enclosure_of_the_frozen_test_floor_is_strictly_positive
    fate: PENDING
```

### 8.4 Two representations and the cheapest decisive task

| Representation | Consumer-facing object | Ordinal kill-power / cost | Main risk |
|---|---|---|---|
| Scalar Mellin floor plus optional positive corrections | \(F(h)\), (13)--(17), or a finite partial sum of (11) | 9/10 / 3/10 for one test | negative or unresolved floor; loss of cancellation in scalar evaluation |
| Archimedean Sonin-image Gram and full residual | (23)--(26), or [PP2, Lemma 5] for a packet | 9/10 / 5/10 for a fixed source packet | uncertified evaluation vectors or replacing the full residual by a compressed one |

These are representation choices, not new top-level RH suppliers. A negative scalar lower bound does not freeze the second representation.

**One CODEX DIRECTIVE — next bounded transaction, not executed here.** Certify the scalar floor of the **frozen source-defined bump** on the full frequency line, with the exact normalization. First record its closed-window support and, when claiming membership in the literal open-interval class, supply the inward smooth-approximation error. Use the explicit Mellin formulas and a proved Euler tail, such as (14), plus a proved frequency tail, such as (16) or a sharper analytic-transform enclosure. Include special-function, transform, quadrature and normalization errors. No semilocal operator eigensolve is required. Return either a rational/interval lower bound \(L(F)>0\), a strict upper bound \(U(F)<0\), or a zero-straddling interval naming its dominant error. The first certifies the original test inequality; the second rejects only this scalar certificate, after which retain (7)/(11). Do not generate new prime sets or rewrite the source form.

**Mandatory falsifier:** on an exact scalar contraction model verify (4) and the directions in (3); for any later Gram implementation run the parent's \(n=4/3\) full-residual plant. Source-density negativity, a nonpositive alleged Gram lower bound, a missing tail, or a clipped/rescaled operator is a hard failure of certification.

**Success code:** `SCALAR_FLOOR_FROZEN_TEST_FULL_LOWER_ENCLOSURE`.
**Unresolved code:** `SCALAR_FLOOR_FULL_LINE_ENCLOSURE_GAP`.
**Certificate-only counterexample code:** `SCALAR_FLOOR_SUFFICIENT_TEST_REFUTED_NOT_SOURCE_MARGIN`.
No Lean edit, new numerical run, Aristotle call, queue mutation, or route promotion occurs in this adjudication.

### 8.5 Consumer-first dependency record

**DOWNSTREAM_CONSUMER:** the unchanged Weil criterion on all complex compact smooth tests.

**ACTUAL_CONSUMER_REQUIREMENT:** nonnegativity of the actual Weil form on that entire class. This request studies a restricted prime-carrying minus-lobe comparison.

**ORIGINAL_REQUESTED_OBJECT:** an all-class scalar floor sign and an accurate source angle-density evaluator.

**ORIGINAL_OBJECT_IS:** `NOT_NECESSARY` for the terminal consumer. In particular \(F\ge0\) is sufficient, not necessary, even for the restricted comparison.

**KNOWN_WEAKER_INTERFACES:** a nonnegative finite partial sum of (11) on a test; the exact margin certified via (23)--(26); or a packet certificate plus a separate full test-space complement/coupling theorem. These reach their explicitly stated test or class, not all compact tests by implication-free extrapolation.

**FAILURE_TYPE:** `NO_DERIVATION` for (SF-CLASS); `NO_SOURCE` for a complete numerical enclosure at the evidence cutoff; `OTHER` for the demonstrated truncation/source-invariant mismatch; `INCOMPATIBILITY` for equal zero infima under the positive constant plant shift and exact unit-endpoint limits at fixed S.

**EPISTEMIC_STATUS:** scalar/all-class signs and numerical enclosures are `RESEARCH_DEBT`. Only the precisely incompatible theorem shapes are rejected. Neither the source phase class nor any RH route family is declared dead.

**NOVELTY_AXIS:** preserve the negative mode correction as a sum of positive contributions to the margin; move the exact inverse to the finite-Euler image metric with an explicit lower bound. No historical priority is asserted.

**REOPEN_TRIGGER:** a certified floor/margin enclosure, an exact source counterexample to (SF-CLASS), or a proof on the original test class with its full complement. The proposed per-prime angle-count law needs a declared threshold and a separate source theorem; more extrapolated eigenvalues alone do not establish it.

### 8.6 Publication gate and closeout

The independently completed draft was hashed before publication. Creation at the exact expected path then failed with GitHub HTTP 422 because the other authorized judge session had concurrently created that file at commit `7333a9abf90954ae7c81c4849769ba8254560550`, blob `9a96b510e7b35e30ffea982b4f14497b6d82584c`. That closed verdict is not overwritten. This second independent verdict is instead published as the single new artifact `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SCALAR_FLOOR_AND_SEMILOCAL_CONDITIONING_2026-09-07_INDEPENDENT_66cc75a1.md`; the exact-path delivery requirement is therefore NOT fulfilled by this session. The concurrent header and publication metadata were read only after the independent draft was complete; none of its derivations was used as a mathematical input. Both reviews remain available as separate files.

The publication receipt reports the actual commit and blob after the write/readback. No Lean source, Lean blob, build, axiom profile, or interval verification is claimed. The gate checks the request ID, declared actual path, header, and one-file diff; it changes publication status only.

```yaml
META_CLOSEOUT:
  PROGRESS_CLASS: PROOF_PROGRESS
  COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
  ROUTE_SCORE: 5
  WHAT_BECAME_SMALLER:
    - inverse_free_scalar_floor_has_a_proof_and_positive_packet_correction
    - unspecified_scalar_tail_constants_replaced_by_explicit_conservative_bounds
    - semilocal_inverse_conditioning_replaced_by_known_finite_Euler_Gram_bounds
    - plant_logic_reduced_to_one_exact_constant_shift
  SCOPED_REJECTIONS:
    - claim: both_true_and_planted_infima_equal_zero
      KILL_SCOPE: THEOREM_SHAPE
      KILL_EVIDENCE_KIND: exact_incompatibility
      evidence: equation_31_with_delta_M_positive
      SCOPE: ABSTRACT
      VERIFIER: PAPER
    - claim: exact_unit_endpoint_limits_at_fixed_finite_S_as_only_J_increases
      KILL_SCOPE: THEOREM_SHAPE
      KILL_EVIDENCE_KIND: source_uniform_strict_defect_bound
      evidence: equations_18_to_20
      SCOPE: ABSTRACT
      VERIFIER: PAPER
  MUST_NOT_RECUR:
    - call_J_spread_a_rigorous_error_bound
    - infer_plant_failure_from_a_lower_bound_on_the_true_margin
    - use_an_out_of_contraction_truncation_in_the_true_mode_identity
    - discard_approximate_modes_without_a_source_error_budget
    - call_a_normalized_Rayleigh_quotient_a_Hermitian_form
    - infer_exact_low_frequency_insensitivity_from_small_mass
    - infer_F_ge_zero_from_modulus_peak_placement_or_a_zero_limit
    - claim_a_finite_test_certificate_before_all_scalar_errors_are_enclosed
  CURRENT_SMALLEST_GAP:
    finite_test: full_source_scalar_floor_lower_enclosure
    all_class: SF_CLASS_or_the_weaker_R_SIGN_with_positive_correction_retained
  DISCRIMINATOR:
    scalar_test: full_interval_for_F_not_only_a_center_value
    source_counterexample: strict_upper_envelope_for_mathfrak_m_below_zero
    false_factor: compare_full_margin_interval_to_delta_M_interval
  MEMORY:
    target: REQ-2026-09-07-SCALARFLOOR
    status: PROGRESS
    invariant_learned: nonpositive_mode_terms_give_lower_certificates_but_not_upper_certificates
    next_decisive_test: certify_one_full_line_scalar_floor_without_semilocal_inverse
```
