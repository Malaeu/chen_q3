# STATUS: TRY_SHIFT_EXPLICIT_SCREW_RESOLVENT_AND_SIGNED_QUOTIENT
```yaml
OPERATIVE_CLASS: TRY_SHIFT_EXPLICIT_SCREW_RESOLVENT_AND_SIGNED_QUOTIENT
PRIMARY_COUNT: 1
SCOPE: ABSTRACT
VERIFIER: PAPER
REQUEST_ID: REQ-2026-09-08-SCREW
BOUNDARY_ID: GOAL058_ZERO_SIDE_QUOTIENT_VERSUS_SUZUKI_CANONICAL_SYSTEMS
RESULT:
  OVERALL: PARTIAL_WITH_PRECISE_REMAINDER
  Q1: PARTIAL_WITH_PRECISE_REMAINDER
  Q1a_DICTIONARY: PROVED_ON_CLASS
  Q1b_DE_BRANGES_SIGN: OBSTRUCTION_NAMED
  Q1c_ERRATUM_CROSSWALK: PARTIAL_WITH_PRECISE_REMAINDER
  Q2: PARTIAL_WITH_PRECISE_REMAINDER
  Q2a_FIRST_PRIME_OPERATOR: PROVED_ON_CLASS
  Q2a_LOWEST_EIGENVALUE_KINK: OBSTRUCTION_NAMED
  Q2b_LIMIT_DICHOTOMY: PROVED_ON_CLASS
  Q2b_UNCONDITIONAL_ZERO_LIMIT: PARTIAL_WITH_PRECISE_REMAINDER
  Q2c_POSITIVE_BASIS_FROM_SHIFTED_BRICKS: ATTEMPT_REFUTED_WITH_EXACT_COUNTEREXAMPLE
  Q3: COMPUTATION_SPECIFIED
REQUEST_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  COMMIT: a367e9e88249b356c33774dc6ce182224c5fc72c
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_SCREW_2026-09-08.txt
  GIT_BLOB: daeba713543f9a012303ede37a03f6759bc5ef55
  SHA256: c42687ae54f7b0f35095fd28b8d29cd220771d1c0ff29ab45810e26fe1ea75f2
  BYTES: 15403
  LINES: 69
  FINAL_LF: true
  GITHUB_CONNECTOR_FETCHED: true
  SHA256_AND_GIT_OBJECT_SHA1_RECOMPUTED: true
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
SOURCE_BOUNDARY:
  REPOSITORY_EVIDENCE_PIN: a367e9e88249b356c33774dc6ce182224c5fc72c
  SUZUKI_2606_VERSION_IN_REQUEST: v1
  SUZUKI_2606_V2_READ_SEPARATELY: true
  SUZUKI_2301_VERSION_READ: v3
  SUZUKI_2206_VERSION_READ: v4
  AUTHOR_ACCEPTANCE_OF_PROJECT_ERRATUM_VERIFIED: false
DECISIONS:
  UNCONDITIONAL_H_W_AS_POSITIVE_COMPLETION_EXISTS_IN_CITED_DEFINITION: false
  PROJECT_WEIGHTED_QUOTIENT_AND_H_W_IDENTICAL_WITHOUT_SIGN: false
  CONDITIONAL_Q_COMPLETION_OF_PROJECT_QUOTIENT_IS_H_W: true
  UNCONDITIONAL_SIGNED_QUOTIENT_REALIZATION: absolute_operator_completion_with_fundamental_symmetry
  SUZUKI_WINDOW_POSITIVE_METRIC: Q_minus_sigma_L2_squared
  SHIFT_SIGMA_IS_SUPPRESSED_IN_W_NOTATION: true
  FIRST_PRIME_PERTURBATION_OF_A: infinite_rank_partial_shift_plus_adjoint
  FIRST_PRIME_A_PERTURBATION_NORM: log_2_over_sqrt_2_for_every_positive_overlap
  FIRST_PRIME_G_PERTURBATION_HS_UPPER: w2_times_overlap_squared_over_sqrt_6
  LOWEST_EIGENVALUE_NONINCREASING: true
  UNCONDITIONAL_LOWEST_EIGENVALUE_LIMIT_AT_MOST_ZERO: true
  LIMIT_DICHOTOMY: zero_if_RH_and_minus_infinity_if_not_RH
  ACTUAL_BRANCH_OF_DICHOTOMY_DECIDED: false
  NULL_FAMILY_IDENTIFIED_AS_LIMIT_OF_GROUND_EIGENFUNCTIONS: false
  HILBERT_SPACE_ISOMORPHISM_IMPLIES_SHIFT_INDEPENDENT_W_ZEROS: false
  LITERAL_ALL_C_HOLOMORPHIC_GAUGE_LIMIT: impossible_for_both_printed_meromorphic_targets
  COROLLARY_1_6_LOGICAL_IMPLICATION_REFUTED: false
  DDF_TYPE_SOURCE_POSITIVE_QUOTIENT_BASIS_CONSTRUCTED: false
CLOSES: [REQ-2026-09-08-SCREW]
CLOSED_RESEARCH_QUESTIONS:
  - signed_versus_positive_quotient_dictionary
  - exact_first_prime_onset_and_its_operator_topology
  - lowest_eigenvalue_monotonicity_and_limit_dichotomy
  - shifted_basis_sign_accounting
  - literal_all_plane_limit_and_abstract_shift_independence_shortcuts
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
  INTERVAL_CERTIFICATE_RUN: false
  LEAN_EDIT: false
  ARISTOTLE_SUBMISSION: false
  EMAIL_ACTION: false
  QUEUE_OR_ROUTE_STATE_EDIT: false
PUBLICATION:
  AUTHORIZED_WRITE_SCOPE: VERDICT_DOC_ONLY
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SCREW_2026-09-08.md
  OLD_DOCUMENTS_OVERWRITTEN: false
  COMMIT_AND_READBACK: delivery_receipt
  PUBLICATION_IS_NOT_MATHEMATICAL_VALIDATION: true
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## 0. Decision and source inventory

The proposed DDF analogy identifies a legitimate question: can the **signed quotient** be represented in positive coordinates while preserving its form? The present papers do not supply that answer unconditionally. They supply two different positive constructions: a global surrogate norm, and a finite-window norm obtained by subtracting a spectral shift. Neither is the unshifted Weil form merely because its kernel or its spectrum looks appropriate.

The decisive distinction is
\[
 T_{a,\sigma}=A_a-\sigma I>0,\qquad
 \|f\|_{a,\sigma}^2=Q(f)-\sigma\|f\|_2^2,
 \qquad \sigma<\lambda_a.                                      \tag{S1}
\]
The parameter called \(\lambda\) in Suzuki (1.9) is denoted \(\sigma\) here; it is **not** the lowest eigenvalue \(\lambda_a\). This parameter also affects the deficiency vectors defining W. Restoring it gives \(W(a,\sigma,\theta;z)\).

The main new calculations below are the exact first-prime perturbation, a conditional identification of the completed quotient, an unconditional alternative for that quotient, and a limit dichotomy. They do not prove which sign the actual quotient has. The literal all-plane limit statements additionally need a domain repair: both printed targets have genuine poles. A conditional implication with an impossible premise is not thereby false, but that premise is not a usable convergence target.

### Source keys and status

All repository readings are at the request commit unless otherwise indicated. A cited source claim is labelled **READ** when its indicated text was inspected; **RELAY** means no independent reading of the underlying original is claimed. Proofs labelled **DERIVATION** are calculations of this verdict, not assertions attributed to a paper. All such mathematical claims have [ABSTRACT][PAPER] tags unless another scope is stated.

- **[K], READ:** `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_KERNEL_2026-09-08.md`, especially (K6)--(K26), (K34)--(K39), Section 8.3; source definitions and exact radical. It is a prior PAPER result, not a Lean theorem.
- **[KC], READ:** `docs/routeB_bus/KERNEL_INDEPENDENT_CHECK_2026-09-08.md`, blob `b48f2c355fdead2ca867a712bbb2f1f753376492`; returned audit, including its expressly unverified (K31)/(K33) imports.
- **[ER], READ:** `paper_weil/ERRATUM_NOTE_SUZUKI_DRAFT.md`, blob `4b516f99e2851f9ac60410dbcb7f145c4cac5929`. This named file outside the bus was opened because the request cites it. Its email-delivery and unanswered-letter annotations are RELAY, not an inbox check.
- **[SC]/[AS], READ as cards, not authority over originals:** the two requested Suzuki usage cards. The first describes v1; it cannot silently specify v2's limit.
- **[S26.1], READ:** Suzuki, arXiv:2606.09096v1, Theorems 1.1--1.5, (1.9)--(1.12), Sections 6 and 7. The PDF's printed p.6 was visually checked.
- **[S26.2], READ separately:** arXiv:2606.09096v2, the same statements, new Section 6.3 and Section 7.8. Printed pp.6--7 and the formulas in Sections 6--7 were checked against the versioned text. The request's v1 target is retained when judging its literal claim.
- **[S23], READ:** Suzuki, arXiv:2301.00421v3, Introduction, (1.3)--(1.10), Sections 3.1--3.3, Proposition 4.1, (4.4), Theorem 5.6. PDF p.3 verifies the negative-time wording.
- **[S22], READ:** Suzuki, arXiv:2206.03682v4, Theorems 1.1--1.3, Lemma 2.1 and Proposition 3.1, (3.8). Its screw-kernel criterion is a theorem about an entire test class, not pointwise nonnegativity of a displayed kernel.

**Source findings, compact ledger.** [S23] defines \(H_W\) under RH, not before it; its unconditional spaces are \(H_0,K_0\). Its Theorem 1.1 is conditional and includes a factor \(\pi\). [S26.1/2] proves window real-zero results using (S1), with small-a positivity only for sufficiently small a. Section 7 assumes RH and explicitly calls \(A_\infty\) a formal symbol. Version 2 changes (1.12). [S22] supplies the signed derivative-to-Weil dictionary and makes the global screw property equivalent to the desired sign. These are the imported statements; none is treated as an unconditional sign supplier.

## 1. Q1(a): exact common form, different completions

### 1.1 Conventions and the common test ideal

Use the project convention
\[
 F_f(z)=\int_{\mathbb R}f(x)e^{zx}\,dx,\quad U_bf(x)=f(x-b),
 \quad M_\pm(f)=F_f(\pm1/2).
\]
Suzuki uses \(\widehat f(z)=\int f(x)e^{izx}dx=F_f(iz)\) and linear-first inner products. Our inner products are antilinear first. Consequently the common compact-test identity is
\[
 Q(f,g)=\langle g,f\rangle_W^{\rm Suzuki},\qquad Q[f]=Q_W(f).
                                                               \tag{S2}
\]
This follows by expanding the same geometric distribution, or by the polarized signed explicit formula [K,(K6),(K16); S23,(1.2),(3.3)]. No positive zero sum is used. The factor of two between the printed definitions of \(\xi\) in S26 and S23 does not change its zeros, logarithmic derivative, or either ratio in Section 5. It must not be confused with an extra factor in Q.

Let
\[
 H_c=\{f\in C_c^\infty(\mathbb R):M_+(f)=M_-(f)=0\},
\]
\[
 \mathscr E=\{\mathcal W[f]+\mathcal D[f]<\infty\},\quad
 \|f\|_E^2=\mathcal W[f]+\mathcal D[f],\quad
 \mathcal W[f]=\int e^{2|x|}|f(x)|^2dx,
 \quad \mathscr H=\ker M_+\cap\ker M_-\subset\mathscr E.           \tag{S3}
\]
Here \(\mathcal D[f]=\int_0^\infty A_0(t)\|U_tf-f\|_2^2dt\), with
\(A_0(t)=e^{-t/2}/(1-e^{-2t})\). [K] proves H_c is an E-core, Q is bounded in this norm, and its E-Riesz representative \(A_E\) satisfies
\[
 A_E=A_E^*,\quad \|A_E\|\le65/3,
 \quad \ker A_E=\operatorname{rad}Q=\mathcal N_{\rm pt}.           \tag{S4}
\]
The symbol \(A_E\) is deliberately different from the unbounded ordinary-L2 window operator \(A_a\). Equality of their forms on common tests is not equality of their Riesz operators in different metrics.

**Two constraints must not be confused.** The intermediate space in S26 is \(L_0^2(-a,a)=\{u:\int u=0\}\). It contains \(Df=if'\) because f has Dirichlet boundary conditions. This is not the two-pole ideal \(M_\pm(f)=0\). The operator \(A_a\) acts on the full window L2 space, with poles retained; the project ideal is a restriction of that form.

### 1.2 What exists without a positive sign

Let \(M=\mathcal N_{\rm pt}^{\perp_E}\). The reference quotient \(\mathscr H/\mathcal N_{\rm pt}\) is isometric to M in the E quotient norm. Its **signed** form is
\[
 q_M(u,v)=\langle u,Bv\rangle_E,\qquad B=A_E|_M,\quad\ker B=0.
                                                               \tag{S5}
\]
Thus it is nondegenerate, but not known positive. It is not a pre-Hilbert space with q_M as inner product until positivity has been proved. Isotropic vectors, defined by q_M(u,u)=0, need not be radical vectors in an indefinite form. The two meanings of “null state” cannot be exchanged.

There is an unconditional, explicit signed completion. Define
\[
 \|u\|_{|B|}^2=\langle u,|B|u\rangle_E,
 \qquad J=\operatorname{sgn}B.
\]
Since B is injective on M, this is a norm. The map \(u\mapsto |B|^{1/2}u\) identifies its completion with M: the range is dense because the orthogonal complement of that range is \(\ker |B|^{1/2}=0\). Spectral calculus gives
\[
 J^*=J,\quad J^2=I,\qquad
 q_M(u,v)=\langle |B|^{1/2}u,J|B|^{1/2}v\rangle_E.               \tag{S6}
\]
The right side extends continuously to this completion. This is an unconditional Hilbert reference space with a fundamental symmetry representing the signed form; if both signs occur, it is a Krein-space realization. It is not a positive realization of Q. Its negative spectral subspace vanishes exactly when the original quotient is positive. This construction uses [K]'s signed source operator, not RH or a list of zero locations. [DERIVATION]

The **unconditional** spaces H_0 and K_0 in [S23, Section 3.3] instead use the repaired map
\[
 J_0\psi=\pi^{-1/2}\widehat{\mathcal P_{D\psi}},\qquad
 \|\psi\|_0^2=\|J_0\psi\|_2^2.                                \tag{S7}
\]
This is a positive norm by its definition, after the signed-time repair. Identifying it with Q is the very norm identity in [S23,(1.9),(4.11)]. The repair does not discharge that identity. No bounded extension of J_0 to all of (S3), or unconditional equality of its completion topology with (S6), is assumed here.

### 1.3 The precise conditional isometry

**Theorem. Assuming Q is nonnegative on the full compact test class, the completion of \(\mathscr H/\mathcal N_{\rm pt}\) in the norm \(\sqrt{Q}\), not its E quotient norm, is canonically isometric to Suzuki's H_W.** [DERIVATION; ABSTRACT/PAPER, explicitly conditional premise]

For f in \(\mathscr H\), choose compact pole-null f_j converging in E. Then
\(Q[f_j-f_k]\le(65/3)\|f_j-f_k\|_E^2\), so the f_j define an element of H_W. The map preserves Q; its kernel is exactly (S4). It remains to show its image is dense in H_W even though the initial compact class has two pole constraints.

Choose a nonzero even nonnegative compact smooth b and let
\(m=M_+(b)=M_-(b)>0\). For R>0 put
\[
 b_R^+=m^{-1}e^{-R/2}U_Rb,\qquad
 b_R^-=m^{-1}e^{-R/2}U_{-R}b,
\]
\[
 u_R^+=\frac{b_R^+-e^{-R}b_R^-}{1-e^{-2R}},\qquad
 u_R^-=\frac{b_R^--e^{-R}b_R^+}{1-e^{-2R}}.                    \tag{S8}
\]
Their moment columns are exactly (1,0) and (0,1). Translation invariance of Q and the triangle inequality in the **assumed positive** Q norm give
\[
 \|u_R^\pm\|_Q\le
 \frac{e^{-R/2}}{m(1-e^{-R})}\|b\|_Q\longrightarrow0.
\]
Hence \(f-M_+(f)u_R^+-M_-(f)u_R^-\in H_c\) converges to any compact smooth f in H_W. This proves density and the completed isometry. It does not assert density in a fixed-window E norm. In that norm the moment functionals are continuous and their common kernel is proper.

On the common compact core there is no nonzero global radical: (S4) forces the entire exponential-type transform to vanish at all distinct zeta zeros, and [S22,Lemma 2.1] makes it zero. The noncompact radical appears after enlargement of the domain. Thus the request's “unconditional inner-product space with a radical” is not the definition in [S23] and is not a correct description of its compact core.

### 1.4 Why the ordinary-L2 limit symbol is not our A_E

[K,(K24)--(K25)] proves that translates of the nonzero null function g_0 span a dense subspace of ordinary global L2. A closed positive form on ordinary L2 that annihilated all those translates would therefore vanish identically. This is incompatible with the short-test positive value in [K,(K14)]. Even under positivity, an ordinary-global-L2 closed operator is not obtained by completing this null family.

A useful conditional description makes the distinction exact. Under Q>=0, complete compact tests in \(Q[f]+\|f\|_2^2\). Their map
\[
 f\longmapsto(f,[f])\in L^2\oplus H_W                              \tag{S9}
\]
is isometric and has dense range. Indeed, compact approximants to finite sums of null translates tend to (u,0); their ordinary-L2 spans are dense. Subtracting these limits from (f,[f]) gives (0,[f]), and compact [f]'s are dense in H_W. Therefore this **abstract graph completion** is the full product. Its projection to ordinary L2 is not injective. Its Q-null subspace is \(L^2\oplus\{0\}\), and its quotient is H_W.

This calculation explains, rather than suppresses, [S26,Section 7.1]'s warning that A_infinity is a formal symbol. Our bounded A_E has an actual independently specified metric. Replacing that metric with ordinary L2 is not a harmless re-labelling. The form identity U*U in the global heuristic must be read as a tested quadratic identity, not automatically as the factorization of a densely defined closed ordinary-L2 operator.

## 2. Q1(b,c): de Branges, signed time, and the inherited error

### 2.1 What the de Branges statement actually supplies

Write
\[
 X(z)=\xi(1/2-iz),\qquad E(z)=X(z)+iX'(z),\qquad
 \Theta(z)=E^\sharp(z)/E(z).                                    \tag{S10}
\]
Primes and zeros have not disappeared: X is the specific completed zeta function. The formula for E is unconditional; the positive de Branges/model-space identification in [S23,Theorem 1.1; S26,Section 7.2] is under RH. Real-axis \(|\Theta|=1\) is not the upper-half-plane contractivity required for that identification. Common real zeros, if multiplicities occur, are handled by the standard removal convention; no simplicity hypothesis for zeta is introduced.

The precise normalization in [S23,Theorem 1.1] is
\[
 \|EF\|_{H(E)}^2=\|F\|_{K(\Theta)}^2
       =\pi\|[\mathsf F^{-1}F]\|_{H_W}^2.                       \tag{S11}
\]
Consequently (S8)'s completed conditional isometry, followed by this map and its explicit square-root-pi scaling, is the requested bridge. There is no unconditional positive identification of the signed quotient. The zero-labelled basis in [S26,Section 7.2] is a **conditional** Hilbert--Polya description, not a construction of positive source bricks before the sign.

### 2.2 The negative-time error does not change Q, G_a or A_a

**READ:** [S23] after (1.5) declares an even extension of \(\mathfrak S_t\); after (3.2) it makes the corresponding even extension for \(\mathfrak P_t\). These printed rules conflict with the signed spectral formulas (3.6)--(3.8). [ER] reports the same defect.

Here is an exact detector. If \(\psi\) is even and compact smooth, \(D\psi=i\psi'\) is odd. The even-time definition makes
\(\widehat{\mathcal P_{D\psi}}=0\). Choose such a nonzero bump of sufficiently short support. From the geometric source, the disjoint-translate integral gives
\(Q[\psi]\ge(2\int_d^\infty A_0-c_A)\|\psi\|^2>0\), with d small; the pole term of an even real bump is nonnegative. Thus the even-time map cannot satisfy (1.9). This is a defect of that map, not an actual negative Weil witness. [DERIVATION]

The repair we use is exactly
\[
 \mathfrak P_{-t}(z)=\mathfrak P_t(-z)\quad(t>0),\qquad
 \mathfrak S_t(z)=\frac{i(1+\Theta^\sharp(z))}{2}\mathfrak P_t(z).
                                                               \tag{S12}
\]
One must not also impose \(\mathfrak S_{-t}(z)=\mathfrak S_t(-z)\); its prefactor has its own z-dependence. Under (S12), the signed exponentials yield [S23,(3.7)--(3.8)]. Restoring that algebra does not prove the conditional orthogonality of the F_gamma's in Proposition 4.1.

[S26,Sections 1--6] constructs g, G_a, A_a and W without using the erroneous even-time map, so that defect does not remove its finite-window construction. Its Section 7.2 Fourier-coefficient map (7.3) is consistent with the signed reading; it is not an explicit published acknowledgment or repair of the negative-time sentence. No statement about an author's reply is made.

Section 7.7 inherits a second normalization issue. With the **same** S_t as [S23], equation (4.4) is
\[
 \pi^{-1}\langle\mathfrak S_x,\mathfrak S_y\rangle_2=G_g(x,y).
                                                               \tag{S13}
\]
The last display of [S26.2,Section 7.7] omits \(1/\pi\), although the preceding operator display includes it. Also \(D=i\partial\) contributes an i to its integral formula for U; this phase does not affect a norm square but does affect an asserted equality of maps. We retain (S13), rather than silently changing S. The useful unproved target is the **tested** correctly normalized Gram identity; no claim of a pointwise kernel identity under the literal even extension survives.

## 3. Q2(a): exact onset of the first prime

Everything in this section is a new [ABSTRACT][PAPER] calculation from the printed g and (K6). Put
\[
 L=\log2,\quad w=\frac{\log2}{\sqrt2},\quad a_0=L/2,
 \qquad d=2a-L.
\]
Compare, on the **same window**, the actual source and the source with the prime-2 term deleted. Use a superscript (0) for the latter. For \(a_0<a<\tfrac12\log3\), no other prime power is active and \(a<L\). This same-window comparison is essential: it is not an identification of Hilbert spaces at two different values of a. READ correction to the question: Theorem 1.4 says sufficiently small a, not every a below log(2)/2; the absence of prime terms is not by itself its full positive-simple-even hypothesis.

### 3.1 Continuous screw kernel: a small corner perturbation

The added term is
\[
 g_2(t)=w(|t|-L)_+.
\]
Let H_a have kernel \((|x-y|-L)_+\) on \((-a,a)^2\), and let P_a be the ordinary-mean-zero projection used in S26. Then
\[
 G_a-G_a^{(0)}=wP_aH_aP_a,
 \qquad \|G_a-G_a^{(0)}\|_{HS}\le \frac{w d^2}{\sqrt6}.          \tag{S14}
\]
Proof: in the corner x=a-u, y=-a+v the kernel is \((d-u-v)_+\). The other corner is its transpose, so
\[
 \|H_a\|_{HS}^2
 =2\int_{u,v\ge0,\ u+v<d}(d-u-v)^2\,du\,dv=d^4/6.
\]
Orthogonal projection cannot increase a Hilbert--Schmidt norm. At d=0 the term is identically zero. It is a continuous ramp, not a pointwise jump in g.

### 3.2 Differentiated source: an infinite-rank perturbation of fixed norm

Distributionally,
\[
 g_2''=w(\delta_L+\delta_{-L}).
\]
With \(C_a=1_{(-a,a)}U_L1_{(-a,a)}\), integration by parts on H_0^1, followed by closed-form extension, gives
\[
 \boxed{A_a-A_a^{(0)}=-w(C_a+C_a^*).}                           \tag{S15}
\]
The same difference holds for B_a on its core. No boundary delta was discarded: the Dirichlet core has zero boundary values, and the difference extends as a bounded L2 operator. Differentiation of P_a's constant output contributes zero; D maps into its mean-zero range.

Let
\[
 I_-=(-a,a-L),\qquad I_+=(L-a,a).
\]
These disjoint strips have length d; C_a translates I_- onto I_+. Thus
\[
 C_a^*C_a=1_{I_-},\quad C_aC_a^*=1_{I_+},\quad C_a^2=0,
\]
\[
 \boxed{\|A_a-A_a^{(0)}\|=w\quad(d>0).}                       \tag{S16}
\]
On the two strips, C_a+C_a* is the off-diagonal identity. Its eigenvalues +1 and -1 each have infinite multiplicity. The complement has eigenvalue zero. Consequently this is **not rank one**, and its L2 operator norm does not tend to zero at entry. It converges strongly to zero as the strips disappear (with a fixed-window rescaling if desired). This is fully consistent with (S14): the two differentiations are unbounded operations.

The exact source pairing is
\[
 \Delta Q[f]=-2w\Re\int_{I_-}\overline{f(x+L)}f(x)\,dx,
 \quad |\Delta Q[f]|\le
 w\big(\|1_{I_-}f\|^2+\|1_{I_+}f\|^2\big).                   \tag{S17}
\]
This is the actual endpoint-mass quantity affected by the first prime, not an overlap-fraction L2 operator bound.

**Admissible two-sided detector.** Choose nonzero \(\eta\in C_c^\infty(0,d)\), set \(k=(\partial^2-1/4)\eta\), and normalize \(\|k\|_2=1\). Its two pole moments vanish by integration by parts. The functions
\[
 f_\pm=2^{-1/2}(U_{-a}k\ \pm U_{L-a}k)
\]
are compact smooth, exactly pole-null and unit norm. Equation (S17) gives
\[
 \Delta Q[f_+]=-w,\qquad\Delta Q[f_-]=+w.                       \tag{S18}
\]
These are signs of the **change**, not of the full Q. Their concentrated archimedean energy cannot be dropped. The construction also rules out a claim that the first prime always lowers every direction.

### 3.3 Why this is not yet a kink theorem for lambda_a

For a regular family with continuous endpoint germs, expanding (S17) yields a term proportional to
\(-2wd\Re\{\overline{f(a)}f(-a)\}\). A family supported a fixed distance from the endpoints sees no new term sufficiently close to entry. The actual minimizer may change and its endpoint regularity needs proof. Therefore neither a nonzero kink nor its sign follows from (S15).

On a bounded form-energy set, compactness of the local form embedding into L2 makes the strip masses uniformly small. To see the mechanism, multiplication by a shrinking strip converges strongly to zero in L2; the convergence is uniform on compact subsets by a finite-net argument. Apply it to the relatively compact image of the form-unit ball. Thus an operator-norm jump can coexist with continuous variational eigenvalues. The latter continuity is [S26,Theorem 1.3]; its differentiability is not supplied.

### 3.4 The arithmetic is in W's vectors, not only its scalar normalization

Fix \(\sigma\) below the bottoms of both compared operators, and set
\(T=A_a-\sigma I\), \(T_0=A_a^{(0)}-\sigma I\), \(V=C_a+C_a^*\). The resolvent identity is
\[
 T^{-1}-T_0^{-1}=wT^{-1}VT_0^{-1}.                            \tag{S19}
\]
The two deficiency vectors, before the common normalization, can be chosen as
\[
 v_\pm=T^{-1}e^{\pm x},\qquad v_\pm^{(0)}=T_0^{-1}e^{\pm x},
 \quad v_\pm-v_\pm^{(0)}=wT^{-1}Vv_\pm^{(0)}.                \tag{S20}
\]
Their equal T-norm follows from reflection, which exchanges the two real vectors and commutes with T. Therefore the prime alters the functions entering both Fourier integrals in W. It can also alter \(\lambda_a\), the admissible choice of \(\sigma\), and normalization. There is no theorem that confines it to \(\theta(a)\) or \(\phi(a,z)\). The c_a of (1.2) normalizes a **different**, ground-eigenfunction approximation; it is not an established normalization of W.

For every legal shift the positive metric (S1) still permits the self-adjoint-extension argument for real zeros. That proof is insensitive to whether Q itself has a negative direction; the actual W and its zeros are not thereby independent of the arithmetic or the shift.

A domain precaution is necessary. [S26,Section 6.2] infers L2-continuity from continuity in the stronger T norm; that inference is invalid. The deficiency formula needed here has a weak-form repair, also consistent with v2's evaluation-vector construction in Section 6.3. Define the distribution \(\mathfrak T v\) by testing the continuous form \(t(u,v)\) against compact u. The adjoint eigen-equation is
\(i(\mathfrak T v)'=z\mathfrak T v\). Its solutions are constant multiples of \(e^{-izx}\); invert the coercive form to obtain \(v_z=T^{-1}e^{-izx}\). Conversely these vectors satisfy the adjoint identity by integration by parts on u. No assertion that v' and (A_av)' separately lie in L2 is needed. This repairs the relevant step, not every domain assertion in Section 6.2.

## 4. Q2(b): radical, lowest eigenvalues and the exact limit alternatives

### 4.1 Monotonicity is unconditional

By [S26,Corollary 1.2],
\[
 \lambda_a=\inf_{0\ne f\in C_c^\infty(-a,a)}Q[f]/\|f\|_2^2.
\]
If b>a, every such test for a is legal for b and has the same geometric source value. Hence
\[
 \boxed{\lambda_b\le\lambda_a.}                               \tag{S21}
\]
This is a derivation from support inclusion, not a claim that continuity alone implies monotonicity.

Let g_0 be [K,(K24)]'s nonzero theta null test. Its exactly pole-null compact approximants g_{0,R} converge in E and in physical L2, so
\[
 Q[g_{0,R}]/\|g_{0,R}\|_2^2\longrightarrow0.
\]
The denominator tends to a nonzero number. Taking supports large enough in (S21) proves
\[
 \boxed{\lambda_\infty:=\lim_{a\to\infty}\lambda_a\le0}          \tag{S22}
\]
in the extended reals. No nonnegativity of the approximating values has been used. The request's “ALIGN gave 0+ unconditionally” is not the parent conclusion: it gave the one-sided obstruction, not approach from above.

If Q>=0, (S22) yields \(\lambda_\infty=0\). Conversely, if \(\lambda_\infty=0\), monotonicity gives \(\lambda_a\ge0\) for every a, hence full compact-test positivity. Thus proving this exact zero limit would settle the sign; the near-null family proves only one direction.

### 4.2 Stronger alternative if an off-line zero exists

There is a useful sharper conclusion, derived here from [K,(K19)--(K23a)]. If an off-line centered zero exists, choose one \(\lambda=\alpha+i\beta\) with \(\alpha>0\), and \(j\lambda=-\alpha+i\beta\). Those formulas construct rapidly decreasing, exactly pole-null tests h_lambda and h_jlambda, normalized to have transform value 1 at their own distinct zero and 0 at every other distinct zero. Multiplicity m is retained.

For T>0 put
\[
 u_T=e^{-i\beta T}U_T h_\lambda
          -e^{i\beta T}U_{-T}h_{j\lambda}.
\]
The only nonzero zero evaluations are \(e^{\alpha T}\) and \(-e^{\alpha T}\). The **signed** formula gives exactly
\[
 Q[u_T]=-2m e^{2\alpha T},\qquad
 \|u_T\|_2^2\le(\|h_\lambda\|_2+\|h_{j\lambda}\|_2)^2=:C.
                                                               \tag{S23}
\]
All moments remain zero. For each fixed T, approximate u_T in E by compact pole-null tests; source continuity and physical-norm convergence preserve any prescribed strict negative upper value. Letting T grow therefore forces \(\lambda_\infty=-\infty\). No uniform cutoff error in T is assumed: choose a compact approximation after fixing T, which is sufficient for the variational conclusion.

We have proved the dichotomy
\[
 \boxed{\lambda_\infty=0\ \text{if RH holds};\qquad
        \lambda_\infty=-\infty\ \text{if RH fails}.}            \tag{S24}
\]
[COFINAL_FAMILY][PAPER; derivation with conditional alternatives.] This does not choose either branch. It supplies neither an actual off-line zero nor an actual negative Q witness. Appendix B completes the cutoff-decay point explicitly flagged in [KC].

### 4.3 What the null family becomes

Under (S8)'s conditional identification, every g_k in the project radical represents **zero in H_W**, not a nonzero oscillator basis state. Its compact approximants have small Rayleigh value, not necessarily small ordinary-L2 residual, and need not be lowest eigenfunctions. The exact control \(\operatorname{diag}(-1,1)\) on \((1,1)/\sqrt2\) has Rayleigh value zero and residual norm one. Even in the positive case, multiple nearly-null directions and changing supports prevent a conclusion about a unique limiting ground profile without a separate spectral-projection theorem.

Nor does \(\lambda_a\to0\), conditionally known under RH, supply uniform resolvent estimates in (S20) at shift zero. The factor \(1/\lambda_a\) can grow. The two source vectors may have special cancellations, but their rates must be proved on those vectors; they do not follow from null-family membership.

## 5. Q2(a,c): the limit needs version, domain and shift repair

### 5.1 The two printed targets are different

**READ, version lock:** [S26.1,(1.12), PDF p.6] asks for
\[
 R_1(z)=z^2\frac{\xi(1/2-iz)}{\xi_s'(1/2-iz)}.
\]
**READ separately:** [S26.2,(1.12), PDF p.7] replaces it by
\[
 R_2(z)=\frac{\xi(1/2-iz)}{\xi(1/2-iz)+\xi_s'(1/2-iz)}
       =X(z)/E(z).                                             \tag{S25}
\]
Section 7.8 of v2 gives an RH-conditional motivation for theta=pi. Neither version exhibits an unconditional pair theta(a),phi(a,z) proving the limit. Both displays say all compact subsets of C; finiteness of phi alone does not supply holomorphy for a Hurwitz argument.

**A precise literal obstruction, not a route-wide kill.** R_1 has genuine poles. Take two consecutive positive real zeros of the real function X (existence of infinitely many critical-line zeros is unconditional; NIST DLMF 25.10(i)). Between them X has a nonzero extremum t_*. Then X'(t_*)=0, X(t_*)!=0 and t_*!=0, so R_1 has a pole.

R_2 also has a genuine pole, independently of RH. For real s<0, \(\xi(s)=\xi(1-s)>0\). Write \(L_\xi(s)=\xi_s'(s)/\xi(s)\). At s=-1,
\[
 L_\xi(-1)=-L_\xi(2),\quad
 L_\xi(2)=\frac32-\frac12\log\pi-\frac12\gamma_E+
                          \frac{\zeta'(2)}{\zeta(2)}<1.
\]
The strict inequality uses \(\log\pi>1\), \(\gamma_E>0\), and the negative logarithmic derivative from the convergent Euler product. As s tends to minus infinity, the functional equation and Stirling's logarithmic derivative give \(L_\xi(s)\to-\infty\). Thus some s_*<-1 has \(1+L_\xi(s_*)=0\), while \(\xi(s_*)>0\). Its corresponding point \(z_*=i(s_*-1/2)\) is a nonremovable pole of R_2. [DERIVATION; standard identities recorded in Appendix A]

An ordinary locally uniform limit of holomorphic, finite-valued functions on all of C cannot have either pole. Even uniform convergence on a closed curve surrounding a pole is incompatible with globally holomorphic approximants: multiply by a power of (z-z_*) if necessary and use Cauchy's integral to detect the nonzero Laurent coefficient. Therefore merely deleting the pole point while retaining every surrounding compact curve does not fix a globally holomorphic-gauge formulation.

This refutes **the literal all-plane holomorphic-gauge approximation target**, not the logical implication “if the stated limit, then RH,” and not the possibility of a different meaningful local or meromorphic spectral limit. The implication can be vacuously true. No pole-based claim is made about the location of zeta's zeros.

A nonvacuous replacement must specify a pole-free domain/cut system and local holomorphic zero-free normalizers, or use genuinely meromorphic approximants with matched poles and a stated convergence topology. For a zero-exclusion proof it suffices to control a disk around each hypothetical off-real zero where the target's quotient singularity is removable and the target has a nonzero analytic germ. The required local normalizers, common source family and convergence are still missing; this is not an asserted repair theorem for (1.12).

### 5.2 Exact counterexample to shift-independence from abstract isomorphism

[S26.1/2, discussion after (1.12)] suggests shift-independent zeros from Hilbert-space isomorphism. This is an expectation, not an intertwining theorem. The following exact model refutes that inference. It is a detector, not a replacement Weil operator.

On L2(-1,1), let \(\mathcal A=I+|1\rangle\langle1|\), and take shifts sigma=0,-1. Both shifted metrics are positive. Put c=1-sigma (so c=1,2) and
\[
 T_c=cI+|1\rangle\langle1|,\qquad
 v_\pm^{(c)}(x)=\frac1c\left(e^{\pm x}-\frac{2\sinh1}{c+2}\right).
                                                               \tag{S26}
\]
These are exactly \(T_c^{-1}e^{\pm x}\); reflection gives equal norms. The derivative on compact smooth tests is symmetric for this translation-invariant kernel. Substituting in the same boundary formula at theta=pi gives
\[
 W_c(z)=-\frac{4i\sinh1}{c}
       \left(\cos z-\frac{2}{c+2}\frac{\sin z}{z}\right).        \tag{S27}
\]
The value at zero is nonzero. No nonzero zero is shared between c=1 and c=2: subtracting the two equations would give sin z/z=0, while cos z could not then vanish. Each has a real positive zero between 0 and pi/2 by its endpoint signs. Thus equivalent positive Hilbert norms and two valid real-zero constructions can yield different spectra at the same theta.

The model kills only the abstract inference. Exceptional shift invariance for the actual source would require a source-specific intertwiner and its boundary-phase transport. Merely allowing a scalar exponential gauge cannot move zeros. An adjustment of theta is an additional object, not something supplied by abstract isomorphism.

### 5.3 What the eigenbasis really diagonalizes

Suppose \(\{e_j\}\) is an orthonormal basis for the positive shifted form t_sigma (in particular, any complete eigenbasis furnished by the relevant self-adjoint realization). For finite coefficient lists,
\[
 Q\left[\sum_jc_je_j\right]
   =\sum_j|c_j|^2+\sigma\sum_{i,j}\overline{c_i}c_j
                                      \langle e_i,e_j\rangle_2. \tag{S28}
\]
The physical Gram matrix in the second term cannot be dropped. For sigma<0, the represented bounded form operator is
\[
 I+\sigma T_{a,\sigma}^{-1},\qquad
 \mu\longmapsto\frac{\mu}{\mu-\sigma}
                                                               \tag{S29}
\]
under the unitary form-space/L2 identification. Its sign is the sign of the eigenvalues mu of A_a. Thus these bricks are positive for t_sigma, not automatically for Q, **already at each finite window**.

The 2D control \(A=\operatorname{diag}(-1,1)\), sigma=-2 gives positive \(T=\operatorname{diag}(1,3)\), but (S29) is \(\operatorname{diag}(-1,1/3)\). A source-negative direction cannot be cured by relabelling a shifted orthonormal basis.

A DDF-type construction in the requested sense would instead have to supply, on a specified dense quotient core, a source-defined map J with
\[
 Q(f,g)=\langle J[f],J[g]\rangle,\qquad
 \ker J=0\text{ on the quotient},
                                                               \tag{S30}
\]
with completeness and domain/transport proved. The sign part of (S30), not just a null kernel, is absent. A source proof of the correctly normalized tested version of (S13) would be one route. No such unconditional identity or positive quotient basis was found in the three read papers. This is a finding about those sources, not an impossibility theorem for every future construction.

There is also a weaker window route: exhibit cofinal a_j and legal shifts sigma_j<lambda_(a_j) with sigma_j->0, plus the exact full-support source realizations. No monotonicity of sigma_j is necessary. Equation (S1) then gives the accepted vanishing-negative-error criterion. Such a source-defined shift law is not presently supplied. Even an all-window sign theorem would not, by itself, prove the stronger specific complex-function limit (1.12).

## 6. Q3: one computation that changes the next task

**Selected computation: SOURCE_W_SHIFT_SENSITIVITY_AT_A1.** It compares the **same actual source** at a=1, theta=pi, and two predetermined safe shifts sigma_1=-32, sigma_2=-33. It does not estimate RH from a finite sample. No run is performed or authorized to enlarge itself in this verdict.

Why this instead of the three suggested alternatives: the first-prime operator change is now determined exactly; a ground/null overlap does not identify the whole quotient; and fitting theta or a gauge to a meromorphic target would test an unstated limit. The suppressed shift is an immediate, falsifiable dependency in the selected construction.

### 6.1 Safe source lock and detector

For a=1 the source has support diameter 2. An elementary budget gives \(A_1>-29I\): c_A<7; at most eight integers m=2,...,9 need be budgeted, each \(\Lambda(m)/\sqrt m\le\log m/\sqrt m<1\); the absolute two-pole form bound is \(2\int_{-1}^1e^x dx=4\sinh1<6\). This gives 7+16+6=29. The pole coefficient is paid once through its two moment functionals. Therefore both shifts are legal, with T_1>=3I, T_2>=4I.

First run the same two-column boundary evaluator on the exact control (S26)--(S27). It must detect the different roots for c=1,2 before its source output is trusted. All comparisons use the physical L2 norm; no truncated-Gram null directions may be discarded without a source residual.

For each shift solve only
\[
 T_j v_{+,j}=e^x,\qquad v_{-,j}(x)=v_{+,j}(-x).
\]
This fixes relative phase and equal T_j norm exactly by symmetry. Form W_j from (1.11), with theta=pi. The original source prime powers, pole part and logarithmic archimedean form are mandatory; a Legendre packet alone is an approximation to these columns, not their definition.

### 6.2 Complete error budget and the two branches

For an approximation y_j in the true operator domain, certify the **full** residual r_j=T_j y_j-e^x in L2. Then
\[
 \|y_j-v_{+,j}\|_2\le\|r_j\|_2/g_j,\qquad(g_1,g_2)=(3,4).
\]
With reflected minus columns and \(\epsilon_j=\|r_j\|/g_j\), the corresponding whole-expression W error on a compact z-set is at most
\[
 \sqrt2 e^{|\Im z|}(|z-i|+|z+i|)\epsilon_j.                    \tag{S31}
\]
Derivative bounds follow by inserting x under the integral; |x|<=1. Include quadrature, source-coefficient, residual and root-isolation errors with outward bounds. Cancellation is assembled before rounding. No fitted gauge is introduced.

Fix the search region 0<z<=10 and isolate the least positive root of each W, certifying absence of earlier roots. Do not silently increase this region or the class. If the designation cannot be certified, return ROOT_NOT_ISOLATED, not a spectral conclusion.

**ЕСЛИ_A:** disjoint rigorous root intervals (equivalently a strictly positive lower separation) demonstrate source shift-dependence for this fixed theta. The next paper task must retain sigma in W and derive a boundary-phase/intertwining law or abandon shift-independence as a shortcut. This is not a negative Q witness.

**ЕСЛИ_B:** both roots are certified and their distance has upper bound at most 10^(-8), with all named errors inside that bound. This is a finite compatibility result only. The next paper task is to derive an exact source identity for the deficiency columns and phase; no shift-independence theorem is inferred. If neither branch is certified, return INCONCLUSIVE_SOURCE_SOLVE_OR_SEPARATION. The discriminator is the signed interval for root separation, with the analytic toy control already passed.

The 10^(-8) number is a prospective diagnostic resolution, not an observed error or a mathematical zero threshold. No claim that this computation settles global positivity is made.

## 7. Dependency contract, alternatives and strongest attack

**DOWNSTREAM_CONSUMER:** unchanged all-compact-test Weil criterion, or its already source-locked pole-null equivalent. **ACTUAL_REQUIREMENT:** full signed source nonnegativity, or a proved vanishing-negative-error family on exhausting supports. **ORIGINAL_OBJECT:** identification of the null quotient with a positive Suzuki realization and a DDF-type basis. **ORIGINAL_OBJECT_IS:** NOT_NECESSARY as a proof method; a direct signed comparison remains allowed.

**KNOWN_WEAKER_INTERFACES:** a legal source shift sigma(a)->0; the complete signed Schur-head bound; or an exact tested Gram identity with a dense source core. Kernel equality alone is not an interface to the sign. **FAILURE_TYPE / EPISTEMIC_STATUS:** NO_DERIVATION / RESEARCH_DEBT for (S30), zero-limit selection, and an actual source complex convergence theorem. **REOPEN_TRIGGER:** an independently proved source shift law, sign-preserving quotient intertwiner, or complete signed head certificate. A genuine negative upper source witness would be equally decisive. No route-family impossibility is asserted.

| Exact failed claim | Evidence | Scope and status |
|---|---|---|
| Equivalent positive shifted norms give identical W zeros at fixed theta | (S26)--(S27), two disjoint real root sets | ABSTRACT/PAPER; THEOREM_SHAPE, COUNTEREXAMPLE |
| A shifted orthonormal expansion is a sum of positive unshifted Q terms | (S28)--(S29), diag(-1,1) control | ABSTRACT/PAPER; THEOREM_SHAPE, COUNTEREXAMPLE |
| First-prime perturbation is rank one or small in ordinary-L2 operator norm | (S15)--(S18) | ABSTRACT/PAPER; THEOREM_SHAPE, exact operator calculation |
| The printed meromorphic target is an all-plane holomorphic-gauge limit | (S25), the two genuine pole proofs | ABSTRACT/PAPER; THEOREM_SHAPE, INCOMPATIBILITY; not a refutation of the corollary's conditional implication |
| Near-null tests alone prove the bottom tends to zero from above | (S22) gives only <=0; (S23) explains the conditional negative alternative | Inference rejected; the actual zero-limit assertion remains UNRESOLVED, not MATHEMATICALLY_DEAD |

These evidence references are fixed within this new artifact. Their kills do not transfer to every possible canonical-system construction or to RH.

| Candidate representation | What must be proved | Kill-power / cost (ordinal) |
|---|---|---|
| Shift-explicit two-column resolvent and boundary function | Same source A_a, full residual, actual shift and phase dependence | 9/10 / 4/10 for the bounded discrimination; selected |
| Signed quotient via |A_E| and sign(A_E) | Eliminate the negative part by a source identity, not by taking an absolute value | 10/10 / 9/10; sign remains open |
| Direct full signed head with the proved tail | Coupled head lower envelope, including every mixed term | 10/10 / 7/10 locally; all-support rule still missing |

**Strongest attack on this verdict:** the new identities identify what a positive construction would need, but they do not supply the missing positivity. Correct. The result is representation and scoped falsification progress. It is not a new analytic RH supplier. The limit dichotomy is a theorem with two alternatives, not evidence selecting the desired one.

## 8. Predictions, sole directive, and closeout

### 8.1 Frozen observer events, preserved before scoring

```text
  P_SPACES_COINCIDE: 0.45 — Q1(a): the unconditional signed-extension H_W is isometric to our ℋ/𝒩 with Q (same test ideal, same pole handling), up to an explicit weight.
  P_FIRST_PRIME_KINK: 0.60 — Q2(a): the crossing a = ½ log 2 produces an explicit change in A_a (a rank-one or kernel-jump term) and the arithmetic enters (1.12) through the normalisation/phase, not through the real-zero property.
  P_LAMBDA_A_TO_ZERO: 0.70 — Q2(b): λ_a → 0 as a → ∞ follows (unconditionally) from the near-null family + cover, and Прошка states it as a theorem or corollary with proof.
  P_DDF_SHADOW: 0.75 — Q2(c): the window eigen-decomposition is unconditional for each a but the passage a → ∞ is exactly the sign of λ_a; no DDF-type basis of the quotient is known or constructible from source data in the literature read.
  P_ONE_COMPUTATION_NAMED: 0.80 — Q3 names one decisive computation with both branches.
```

| Event | Original p | Fate, without changing its meaning |
|---|---:|---|
| P_SPACES_COINCIDE | 0.45 | REFUTED_AS_STATED: H_W's cited positive completion is conditional; (S8) proves the appropriate conditional completed isometry, not the forecast's unconditional identity. |
| P_FIRST_PRIME_KINK | 0.60 | PARTIAL: exact onset established; rank-one reading false, the ramp and infinite-rank partial shift distinguished; arithmetic enters the deficiency vectors as well as any normalization. A kink of the lowest eigenvalue is not proved. |
| P_LAMBDA_A_TO_ZERO | 0.70 | NOT_ESTABLISHED: only the unconditional one-sided implication and (S24)'s dichotomy are proved. The claimed inference from near-nullity is invalid; the actual zero-limit theorem is not refuted. |
| P_DDF_SHADOW | 0.75 | PARTIAL: unconditional positive shifted construction preserved. Its basis does not yet give positive Q pieces at finite a; the specific global function limit needs more than the sign. No positive source quotient basis is supplied by the read papers. No impossibility of constructing one is claimed. |
| P_ONE_COMPUTATION_NAMED | 0.80 | CONFIRMED_AS_SPECIFICATION: Section 6 fixes one two-shift, two-column source test and both outcome branches. It has not run. |

### 8.2 Own KERNEL registrations against the returned audit

| Registration | Original p | Fate |
|---|---:|---|
| P_KERNEL_RIESZ_RADICAL_AUDIT_SURVIVES | 0.85 | CONFIRMED_AS_RETURNED_PAPER_AUDIT, with the uniform cutoff-decay point made explicit in Appendix B here. Neither the reference metric nor the sign claim is changed. |
| P_KERNEL_L2_TOPOLOGY_OBSTRUCTION_SURVIVES | 0.96 | CONFIRMED: [KC] independently accepts all four density/graph-closure steps of (K25). |
| P_KERNEL_FIXED_S_RANK_ONE_FALSIFIER_SURVIVES | 0.91 | PARTIAL: [KC] accepts (K30) and the projection premise, but expressly does not verify (K31) and (K33)'s Euler prefactor. The whole frozen two-part event is not upgraded to fully confirmed. |

The checker's numerical agreements are not new interval certificates. Its phrase that a classical import “carries no risk” is not adopted; conventions and domains remain load-bearing. No posterior replaces an original probability.

### 8.3 New prospective registrations

- P_SCREW_FIRST_PRIME_SHIFT_AUDIT, p=0.94: an independent source audit accepts (S14)--(S20), including the infinite rank, fixed perturbation norm and pole-null two-sided detector.
- P_SCREW_QUOTIENT_AND_LIMIT_DICHOTOMY_AUDIT, p=0.88: the completion dictionary and (S24) survive without an unconditional positivity premise.
- P_SCREW_SOURCE_SHIFT_SEPARATED, p=0.70: if the bounded test of Section 6 successfully isolates both designated roots with complete enclosures, their intervals are disjoint. Failure to isolate is UNRESOLVED, not confirmation or refutation.

These are registered for **future** review or execution. The present derivations did not receive additional pre-test probability registrations beyond the frozen observer events; no retrospective blind-success score is assigned to them. The observer's original events and parent registrations were frozen before this response.

### 8.4 One CODEX DIRECTIVE

**SOURCE_W_SHIFT_SENSITIVITY_AT_A1.** Execute only the specification of Section 6 after an independent paper check of (S20), the source lower bound and the toy detector (S27). Preserve a=1, theta=pi, shifts -32/-33, reflection normalization and the root-search cap. Return exact source equations, full residual enclosures, outward W/derivative bounds, and the two isolated root intervals. Success is branch A or B exactly as defined; otherwise return the named unresolved status and the first missing error term. Do not fit phi, change theta, scan supports, delete approximate Gram modes, use a finite positive packet as a full floor, edit Lean, send email, or promote route state. No such execution occurred during this adjudication.

### 8.5 Closeout and verification handoff

What became smaller: quotient identity is replaced by the exact completed conditional isometry; the first prime is reduced to one partial shift; the suppressed shift is restored to W; and the zero-limit claim is split into its two rigorous alternatives. What was not closed: a positive basis of the signed quotient, an unshifted all-support sign, or a valid source convergence law.

Must not recur: treat an isotropic vector as radical without proof; complete an indefinite form as a Hilbert norm; promote positive shifted bricks to Q positivity; infer a global ground limit from one null family; compare different versions of (1.12) without notice; or treat compactness of a continuous kernel as operator-norm smallness after two differentiations.

Smallest retained gap: **ALL_SUPPORT_SIGNED_SCHUR_HEAD_LOWER_BOUND**, equivalently a source sign on the same quotient. The new source test addresses whether the canonical-system representation has an additional shift-transport dependency; it does not rename that sign as solved. Progress: REPRESENTATION_PROGRESS and scoped FALSIFICATION_PROGRESS. Cognitive operator: UNIT_AUDIT. Route score: 3. Reopen trigger and discriminator are in Sections 6--7.

Only the EXPECTED_VERDICT_PATH is written on rh_clean, with a [Proshka] commit prefix. The delivery receipt reports commit, parent, blob, SHA-256, byte/line counts and one-file diff. Readback verifies publication only. No Lean file, theorem axiom profile, numerical certificate or kernel gate is claimed. Independent review may ratify or repair these PAPER derivations; it cannot promote RH unless the currently absent all-support sign is actually supplied.

## Appendix A. Exact ledger and convention controls

All entries are [ABSTRACT][PAPER], with no quadrature or eigenvalue run.

A1. For d>0, \(2\int_0^d\int_0^{d-u}(d-u-v)^2dvdu=d^4/6\). Therefore the factor in (S14) is \(1/\sqrt6\), not an empirical fit. The two strips have length d and are disjoint because a<L. Their union covers the entire nonzero part of (S15).

A2. For k=(partial^2-1/4)eta, integrating twice gives \(M_\pm(k)=(1/4-1/4)M_\pm(\eta)=0\). The two translated supports in (S18) are disjoint, so their norm squared is exactly one, and their cross correlation at L is exactly +/-1/2.

A3. In (S8) the moment matrix of b_R^+,b_R^- is [[1,e^(-R)],[e^(-R),1]], with determinant 1-e^(-2R)>0. The inverse in that equation is literal. The Q-norm bound uses positivity only in the explicitly conditional theorem.

A4. On a=1, \(\|e^{x/2}\|_2^2=\|e^{-x/2}\|_2^2=2\sinh1<3\), because e<3 and e^(-1)>0. Thus the absolute two-pole form bound is <6. The function log x/sqrt x has maximum 2/e<1 for x>0, so budgeting the eight integers 2 through 9 costs <16 in the full signed prime form. With c_A<7, Q>-29I follows. Inactive prime powers can be overbudgeted, never added to the actual source matrix. These yield gaps 3 and 4 for the selected shifts.

A5. Let X(z)=xi(1/2-iz). Then \(\xi_s'(1/2-iz)=iX'(z)\). Equation (S25) therefore uses X+iX', not X+X'. On real s>1, logarithmic differentiation of the convergent Euler product gives zeta'/zeta<0. Logarithmic differentiation of the completed function gives
\[
 \xi'/\xi(s)=1/s+1/(s-1)-\tfrac12\log\pi
                  +\tfrac12\psi(s/2)+\zeta'/\zeta(s).
\]
The real asymptotic psi(t)=log t+O(1/t) and zeta'/zeta(s)->0 imply this tends to +infinity as s->+infinity. Functional reflection gives the negative infinity used in Section 5. These inputs are standard exact identities/asymptotics, not facts about zero locations. NIST DLMF 25.2.11, 25.4, 5.11.2 are the convention sources.

A6. Sherman--Morrison in (S26) can be verified without an inverse theorem: multiply its expression by cI+|1><1| and use integral e^x=integral e^(-x)=2sinh1, integral1=2. The integrals in (S27) use \(1+iz=i(z-i)\), \(-1+iz=i(z+i)\), and \(\widehat1=2\sin z/z\). At z=0 its bracket is c/(c+2)>0; at z=pi/2 it is negative. Subtracting the c=1,2 root equations is the exact detector, not a floating root search.

A7. The sign-preserving multiplier in (S29) is \(\mu/(\mu-\sigma)\), whose denominator is positive for every spectral mu of A_a. It cannot turn a negative mu positive. This remains true on the full form space, not merely on a finite truncation.

## Appendix B. Completing the uniform cutoff decay noted by KERNELCHECK

[KC] accepts the kernel argument but asks for a uniform vertical-decay constant. The following supplies one. It also avoids differentiating the nonsmooth weight \(e^{|x|/2}\) in the checker's proposed formula.

Let v=J_lambda^r Phi as in [K,(K19)--(K21)]. Its derivatives are doubly exponentially decreasing. Fix a smooth cutoff chi with compact support, equal to 1 near zero, and put chi_R(x)=chi(x/R), R>=1. Define
\[
 a_R=(\partial_x^2-1/4)(\chi_R v),\quad
 D_k=\|\chi^{(k)}\|_\infty,\quad
 V_j=\int e^{|x|/2}|v^{(j)}(x)|dx<\infty.
\]
The D_k bound the corresponding derivatives of chi_R uniformly. For j=0,...,4 set the explicit finite constants
\[
 B_j=\sum_{k=0}^{j+2}{j+2\choose k}D_k V_{j+2-k}
       +\frac14\sum_{k=0}^{j}{j\choose k}D_k V_{j-k}.
\]
Leibniz gives \(\int e^{|x|/2}|a_R^{(j)}|\le B_j\). For |s|<=1/2,
\[
 \|\partial^q(e^{sx}a_R)\|_1
 \le\sum_{j=0}^q{q\choose j}2^{-(q-j)}B_j.
\]
Use (1-partial^2)^2 and integration by parts against e^{iTx}; all boundary terms vanish. With
\[
 C_4=B_0+2\sum_{j=0}^2{2\choose j}2^{-(2-j)}B_j
                  +\sum_{j=0}^4{4\choose j}2^{-(4-j)}B_j,
\]
one obtains
\[
 \boxed{|F_{a_R}(s+iT)|\le C_4(1+T^2)^{-2}}
 \quad(R>=1,\ |s|<=1/2).                                     \tag{S32}
\]
C_4 depends on the fixed zero, its order and the fixed cutoff, not on R. These are independently defined finite integrals, not a supremum of the unproved target. The unconditional O(T log(2+T)) zero count makes this bound summable over zeros. It justifies the dominated passage used in [K,(K23)] and (S23). No uniformity in the unknown zero or in T's separate translation parameter in (S23) is asserted or needed.

## 9. PROSHKA'S OWN LINE

The quotient is the right place to ask the sign question, but its reference norm matters.
The weighted project quotient exists before positivity; Suzuki's H_W does not use that norm.
I chose the shift-explicit dictionary because it exposes a hidden paid energy in every finite brick.
A positive shifted norm is useful machinery, not a source proof for the unshifted form.
The nearest alternative was to compute the first-prime kink of the lowest eigenvalue.
The exact partial-shift calculation answers the operator question before any eigenvalue scan.
It also shows why a small continuous-kernel perturbation need not be small after differentiation.
The other alternative was to fit a phase and an exponential gauge to the limiting zeta ratio.
That would be premature while the printed target has poles and the shift is suppressed.
The first move beyond this batch is to test the actual source for shift dependence.
Disjoint certified zero intervals would force the shift into every subsequent convergence contract.
Nearly coincident intervals would instead motivate a source intertwiner, not prove one.
The second move is to derive the tested Gram identity in a topology containing the quotient core.
A wrong pi factor, even-time extension, or unproved ordinary-L2 closure would kill that representation.
Neither failure would kill a direct signed-head proof of the same source sign.
I would ask for two complete deficiency-resolvent columns rather than another ground-state plot.
Their residuals must include the continuum complement and their boundary normalization must be fixed.
I would also ask that any later limit request specify the holomorphic domain before choosing a gauge.
The owner's form/radical/quotient frame is useful because it separates vanishing from sign.
What surprised me is how directly the first prime survives as an infinite-rank edge exchange.
Its continuous primitive looks small, while its differentiated L2 norm stays fixed.
What I distrust is the move from identical kernels to identical positive quotient geometry.
An absolute value of an operator provides a norm but deletes precisely the unresolved inertia.
I also distrust describing a radical element as a nonzero physical oscillator after quotienting.
It represents zero there, even when its original ordinary-L2 norm is large.
The near-null family does not select the bottom eigenfunction or decide the sign of the limit.
The zero/minus-infinity dichotomy makes that distinction especially explicit.
A DDF-type basis would have to preserve Q, not just produce real characteristic roots.
The source identities here narrow that task but do not deliver such a basis.
The next result should either identify the shift transport or pay the signed quotient form itself.

## 10. RESEARCH LOG

This is a source and candidate-certificate audit log, not a transcript of private reasoning. No numerical experiment was performed.

### 10(a). Sources consulted and uses

- READ — SCREW request at the commit/blob in the header, all 69 lines; controlling questions, predictions and publication boundary.
- READ — current PROSHKA_SYSTEM_PROMPT_v2.md, blob in header; intake, immutable artifacts, source/scope and verdict obligations.
- READ — [K], requested KERNEL verdict, (K6)--(K26), (K34)--(K39), Section 8.3 and its stated audit target; reference metric, radical, separating tests and frozen predictions.
- READ — [KC], Sections 0--5; returned audit and its explicit limitations. Its numerical results remain RELAY diagnostics and were not rerun.
- READ — requested SUZUKI_SCREW_USAGE_CARDS.md; v1 roadmap, checked against the originals rather than promoted over them.
- READ — requested SUZUKI_ASPECTS_2206_USAGE_CARDS.md, cards 1--4; derivative-coordinate warning. Its quotations of Yoshida were not treated as a newly read Yoshida source.
- READ — [ER], the specifically cited paper_weil/ERRATUM_NOTE_SUZUKI_DRAFT.md; negative-time proposed repair. Email sent/unanswered is RELAY only.
- READ — https://arxiv.org/html/2606.09096v1 and https://arxiv.org/pdf/2606.09096v1 : (1.3)--(1.12), Theorems 1.1--1.5, Sections 6.1--6.4 and 7.1--7.7; fixed-window definitions and literal original limit.
- READ — https://arxiv.org/html/2606.09096v2 and https://arxiv.org/pdf/2606.09096v2 : (1.9)--(1.12), Sections 6.2--6.4, 7.1--7.8 and 8.5; changed target, evaluation vectors, shift discussion, conditional factorization and normalization.
- READ — https://arxiv.org/html/2301.00421v3 and https://arxiv.org/pdf/2301.00421v3 : Introduction and Theorem 1.1, (1.5)--(1.10), (3.2), (3.5)--(3.9), Proposition 4.1, (4.4), Theorem 5.6; conditional H_W and signed-map surrogate. Negative-time text visually checked on p.3.
- READ — https://arxiv.org/html/2206.03682v4 : Theorems 1.1--1.3, Lemma 2.1, Proposition 3.1 and (3.8); signed screw/derivative/Weil relation and exponential-type uniqueness.
- READ — https://dlmf.nist.gov/25.10 : infinitely many real critical-line zeros, used only for the pole detector for R_1.
- READ — NIST DLMF 25.2.11, 25.4 and 5.11.2: Euler product, xi reflection and digamma asymptotics for Appendix A.5; no zero-location input.
- RELAY — CC20 Appendix C Proposition C.1 (155), as pinned and directly read by [KC]; the pole-null criterion is inherited from [K]/[KC], not claimed freshly downloaded here.
- RELAY — Hodge-index and no-ghost/DDF comparison in the owner's request; used only as the requested analogy. No theorem about a number-field geometric realization or string-theory basis is imported.
- NOT CONSULTED AS EVIDENCE — old conversation exports, unpinned queue entries, new inbox messages, raw numerical output arrays, or an alleged author's response.

### 10(b). Candidate claims tested and not retained

- Unconditional positive identification with H_W: fails at its positive-completion definition; (S5)--(S8) retain the signed and conditional alternatives.
- First-prime rank-one correction: fails at (S16), which has two infinite-dimensional strip eigenspaces.
- Overlap length as the L2 perturbation norm: fails on the normalized pole-null functions (S18).
- Near-null sequence implies zero variational bottom: lacks a lower sign; (S24) preserves both possibilities.
- Abstract Hilbert isomorphism implies W shift-independence: the explicit model (S27) has different zeros.
- Shifted eigenbasis is a positive Q basis: the physical Gram term in (S28) survives and the two-dimensional control has a negative direction.
- Literal all-plane holomorphic-gauge convergence to either printed ratio: fails at a genuine pole, not at a numerical residual.
- Even-time S extension: fails on an even compact test differentiated once.
- Ordinary-global-L2 realization of the null quotient: conflicts with the dense null-translate control; (S9) gives the conditional abstract completion instead.

### 10(c). Intermediate formulas retained for other questions

- The ramp Hilbert--Schmidt bound (S14) is useful for integral-kernel discretization, but does not bound the differentiated source norm.
- The endpoint-mass estimate (S17) can control form-bounded families and onset regularity; it does not alone determine the minimizer's derivative in a.
- The resolvent identity (S19) tracks the prime's effect on each deficiency column without subtracting ill-conditioned independent inverses.
- The remote moment correctors (S8) prove conditional density in the Q completion, but explicitly not in the fixed-window reference topology.
- The amplified off-line pair (S23) supplies the negative branch of the variational dichotomy, conditional on such a zero; it is not an actual counterexample.
- The absolute-operator representation (S6) is an unconditional signed quotient model, but its fundamental symmetry contains the unresolved sign.
- The cutoff constant (S32) supplies the previously abbreviated domination step without differentiating an absolute-value weight.

End of verdict. Only this new document is authorized for remote publication. Every new analytical proof remains PAPER pending independent review; the requested all-support sign remains unproved.
