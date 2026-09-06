# STATUS: TRY_PHASE_CLASS_MIXED_KERNEL_CERTIFICATE_WITH_TENSOR_CROSSWALK
```yaml
OPERATIVE_CLASS: TRY_PHASE_CLASS_MIXED_KERNEL_CERTIFICATE_WITH_TENSOR_CROSSWALK
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-06-PHASEPROOF
BOUNDARY_ID: GOAL058_PHASE_CLASS_INEQUALITY_8_AND_MOLLIFIER_CROSSWALK
RESULT:
  Q1: PARTIAL_WITH_PRECISE_REMAINDER
  Q1a: PARTIAL_WITH_PRECISE_REMAINDER
  Q1b: COMPUTATION_SPECIFIED
  Q1c: PARTIAL_WITH_PRECISE_REMAINDER
  Q1d: PARTIAL_WITH_PRECISE_REMAINDER
  Q2: PARTIAL_WITH_PRECISE_REMAINDER
  Q2a: ATTEMPT_REFUTED_WITH_EXACT_COUNTEREXAMPLE
  Q2b: PARTIAL_WITH_PRECISE_REMAINDER
  Q2c: COMPUTATION_SPECIFIED
REQUEST_LOCK:
  COMMIT: e3dba5975b10ba7dbebbdea948612dd830aaf67a
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_PHASE_CLASS_INEQUALITY_AND_MOLLIFIER_CROSSWALK_2026-09-06.txt
  GIT_BLOB: 1d00e0e9a735c43ac14e6785f2415fce472cc13e
  SHA256: ec050368d9d4bef1185df68a549d58f81ae6d5462b3b968831273c6349ffba7c
  BYTES: 11445
  LINES: 96
  FINAL_LF: true
  SHA256_RECOMPUTED_FROM_FETCHED_UTF8: true
  GIT_BLOB_RECOMPUTED_FROM_FETCHED_UTF8: true
EVIDENCE_CUTOFF: e3dba5975b10ba7dbebbdea948612dd830aaf67a
POST_REQUEST_REPOSITORY_RESULTS_USED: false
BOOTSTRAP_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_SECOND_EXPRESSION
  SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
  TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false
MATHEMATICAL_DELIVERY:
  POLE_NULL_CLASS_PARAMETRIZED_EXACTLY: true
  NU_A_EXPLICIT_SPECTRAL_QUADRATIC_KERNEL: true
  B_VARIANCE_IDENTITY: true
  EXACT_EULER_CUTOFF_LEAKAGE_IDENTITY: true
  DIRECT_MINUS_ONE_SIDED_CERTIFICATE: true
  WHOLE_R1_MINUS_SIGN_PROVED: false
  INFINITE_DIMENSIONAL_SIGN_SUBCLASS_PROVED_AT_CUTOFF_1: false
  WHOLE_R1_MINUS_REFUTED: false
  CCM_QSERIES_JACOBI_IS_G: false
  QS_COEFFICIENT_RING_IS_EXACT_SONIN_EVALUATOR: false
  HS_SQUARE_IS_SINGLE_SOURCE_LINEAR_WEIL_VALUE: false
  TENSOR_SQUARE_CROSSWALK: true
  POLARIZED_SEMILOCAL_MATRIX_SPLIT: true
  HEIGHT_TRUNCATION_AND_POLE_CORRECTIONS_RETAINED: true
  OFF_DIAGONAL_PRIME_SUM_IDENTIFIED_WITH_ANGLE_E: false
  HARDY_LITTLEWOOD_PROVED_NECESSARY: false
  DAVENPORT_HEILBRONN_NATIVE_SONIN_SPLIT: NOT_ESTABLISHED
REPAIRS_TO_REQUEST:
  NU_A_LOWER_BOUND_SIGN: REVERSED_IN_QUESTION_1a
  MONTGOMERY_TAYLOR_CONSTANT: EXTRA_FACTOR_ONE_HALF_REMOVED
  NO_STENCIL_THEOREM_APPLIES_AUTOMATICALLY_TO_RESTRICTED_PHASE_CLASS: false
  SINGLE_PLANT_SURVIVAL_IMPLIES_PURELY_ARCHIMEDEAN_MECHANISM: false
SCOPED_REFUTATIONS:
  - name: CCM_QSERIES_JACOBI_LITERAL_GRAM_IDENTIFICATION
    KILL_SCOPE: THEOREM_SHAPE
    FAILURE_TYPE: INCOMPATIBILITY
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
    evidence: section_3_2_positive_Gram_vs_indefinite_Jacobi
  - name: DROP_PROJECTION_FROM_INVERSE
    KILL_SCOPE: THEOREM_SHAPE
    FAILURE_TYPE: COUNTEREXAMPLE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
    evidence: section_2_5_two_dimensional_exact_plant
  - name: SOURCE_LINEAR_SINGLE_TEST_REPRESENTATION_OF_HS_SQUARE
    KILL_SCOPE: THEOREM_SHAPE
    FAILURE_TYPE: COUNTEREXAMPLE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
    evidence: section_6_3_affine_source_second_difference
CLOSES: [REQ-2026-09-06-PHASEPROOF]
CLOSES_ANALYTIC_RH_SUPPLIERS: []
OPENS: []
REMAINING_SIGN:
  name: SEMITABLE_R1_MINUS_AT_FIXED_CUTOFF_1
  status: UNRESOLVED
  epistemic_status: RESEARCH_DEBT
  exact_requirement: section_2_equation_12
NEW_DERIVATIONS:
  SCOPE: ABSTRACT
  VERIFIER: PAPER
  LEAN_VERIFIED: false
AUDIT_LIMITS:
  NUMERICAL_RUN_PERFORMED: false
  SYMBOLIC_SOFTWARE_EXPERIMENT_PERFORMED: false
  HASH_COMPUTATION_PERFORMED: true
  LEAN_KERNEL_RERUN: false
  RAW_OBSERVER_CERTIFICATES_VERIFIED: false
  ALL_SHELF_SHA256_PREFIXES_RECOMPUTED: false
  TWO_THIRDS_THEOREM_FULL_PROOF_REAUDITED: false
  PAPER_PROOFS_ARE_NOT_INDEPENDENT_KERNEL_CERTIFICATES: true
REVIEW_BOUNDARY: PAPER_PROOF_CONSTRUCTION_AND_ADVERSARIAL_REVIEW
AUTHORIZED_WRITE_SCOPE: VERDICT_DOC_ONLY
EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_PHASE_CLASS_INEQUALITY_AND_MOLLIFIER_CROSSWALK_2026-09-06.md
LEAN_EDIT_PERFORMED: false
QUEUE_OR_SHARED_STATE_EDIT: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## 0. Decision, sources and the actual proof boundary

**The requested inequality is not proved or refuted on its whole class.** The useful output is an exact mixed-kernel representation, a cancellation-preserving one-sided evaluator, and a precise three-lobe extension. Two alleged shortcuts do not survive: the local-factor Jacobi matrix is not the compressed Euler Gram operator, and the pair-correlation Hilbert--Schmidt square is not a source-linear value of the original Weil form on one window-built test. A tensor identity and a polarized matrix identity replace those wrong identifications. These are paper derivations, not a new RH inequality. [ABSTRACT][PAPER]

The request's lower-bound instruction has a sign error. Its displayed (8) is equivalent to

\[
 \nu_a\ge n_0-A_0-J_a-w,
 \tag{1}
\]

not to the negative of the right side. The audit proves identities against (8), preserving the requested target and explicitly correcting this intermediate instruction. No request bytes or predictions are edited.

### Source keys and reading boundary

All repository evidence is read at the request commit unless a parent commit is given explicitly.

- **[ST]** `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SEMILOCAL_TABLE_PHASE_CLASS_2026-09-06.md`, Git blob `80eb2189b7a9de523fb0aec1bbdaa198bb02bba2`: definitions and equations (1)--(14), Theorems 3--4, and the tested trace formula (21). These are prior PAPER derivations to recheck, not axioms supplied by an earlier verdict.
- **[IC]** `docs/routeB_bus/SEMITABLE_INDEPENDENT_CHECK_2026-09-06.md`: independent algebra/analytic checks and diagnostic values. Its own inherited projection and trace-formula assumptions are kept separate from its checks.
- **[SS]** SEMISIGN, commit `59aabc180e35400a13d28481d7141e62c1985e5a`, `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SEMILOCAL_SIGN_MECHANISM_2026-09-06.md`: one-sided inverse series and the different, large-cutoff finite-packet result.
- **[SC]** `docs/routeB_bus/litreview/SWEEP_C_FRESH_TOOLS_FOR_INEQUALITY_8_2026-09-06.md`, especially card C3; **[LC]** `docs/routeB_bus/litreview/LAMZOURI_HILBERT_SIMPLE_ZEROS_2026_USAGE_CARDS.md`. Cards are scouting reports; their operator identifications are tested against the primary definitions below.
- **[CC20]** Connes--Consani, arXiv:2006.13771v1, Section 4, Theorem 4.7 and (83)--(84); Sections 5--6; Appendix D. This is the archimedean Sonin/prolate construction, not a ready semilocal phase inequality.
- **[CCM23]** Connes--Consani--Moscovici, arXiv:2310.18423v2, Section 4, in particular (57)--(59) and its Sonin-space isomorphism. The finite Euler map is bounded invertible, not an isometry.
- **[CCM24]** Connes--Consani--Moscovici, arXiv:2403.01247v1, the cyclic multiplication operator, local-factor measure and its Jacobi recurrence (including the zero-diagonal matrix (3)); the coefficient-integrality assertions concern formal series.
- **[C26]** Connes, arXiv:2602.04022v1, (22) and endnote 11: the fixed-cutoff trace convention used by the parent split.
- **[AF]** Alpöge--Furman, arXiv:2608.13637v2; also the request's separately identified 17-page Anthropic PDF dated 11 August 2026, Sections 1.4, 2, 5 and 7.2. The dated PDF and the later arXiv version are not asserted byte-identical. Definitions of the modulation window and source compression were checked in the PDF, including displayed formulas visually. The analytic second-moment method is not a Dirichlet-polynomial mollifier proof.
- **[L26]** Lamzouri, arXiv:2609.02882v1, Proposition 2.1 and Section 3, including the two-test removal of the pair-correlation weight and the Montgomery--Taylor constant.

The primary papers were checked through their versioned full text, not merely the shelf's abstract summaries. This is a focused object/estimate audit, not independent verification of the full recent two-thirds theorem or its Lean repository. The request's exact UTF-8 text was re-encoded and independently hashed, including the final LF; both hashes and both size counts matched. The other shelf hashes are not all independently recomputed. No new numerical experiment is used. The observer's values retain precisely the diagnostic status stated in the request.

## 1. Fixed objects and an exact parametrization of the pole-null class

Put

\[
 a=\log2,\quad r=2^{-1/2},\quad w=ar,\quad
 \delta=(\log3-\log2)/8,\quad I=(-\delta,\delta).
\]

On the log-line Hilbert space, use

\[
 U_cg(x)=g(x-c),\quad T_hg=h*g,\quad
 \widehat h(\xi)=\int h(x)e^{-i\xi x}\,dx.
\]

The Fourier transform with multiplier \((2\pi)^{-1/2}\) is denoted by \(\mathcal F\); convolution \(T_h\) has multiplier \(\widehat h\). Write \(\mathsf A=U_{a/2}-U_{-a/2}\) for the two-lobe map, avoiding confusion with the pole functional \(A_-(h)\). Define

\[
 \mathcal H_{00}(I)=\{h\in C_c^\infty(I;\mathbb C):
             \int h(x)e^{x/2}dx=\int h(x)e^{-x/2}dx=0\}.
\]

The target is \(L_2(\mathsf Ah)-n_2(\mathsf Ah)\ge0\) for every such \(h\), at cutoff **exactly 1**. For nonzero \(h\), let \(H=\|h\|_2^2\) and \(v_-=\mathsf Ah/\sqrt{2H}\). The lobes are disjoint, their total diameter is \(a+2\delta<\log3\), and \(C_{v_-}(a)=-1/2\). Thus no higher power of 2 contributes, and the pole terms vanish. [ABSTRACT][PAPER]

**Lemma 1 (no missing part of the pole-null class).** The map

\[
 \eta\longmapsto h=(\partial_x^2-1/4)\eta
 \tag{2}
\]

is a bijection from \(C_c^\infty(I;\mathbb C)\) onto \(\mathcal H_{00}(I)\). It preserves realness and parity.

**Proof.** Integration by parts gives both moment conditions. Conversely set

\[
 \eta(x)=\int_{-\infty}^x2\sinh((x-t)/2)h(t)\,dt.
\]

Differentiating twice gives \(\eta''-\eta/4=h\), since the first derivative of the kernel at zero is 1. Left of the support this function is zero. Right of the support it equals
\(e^{x/2}A_-(h)-e^{-x/2}A_+(h)=0\). It is smooth, supported inside the convex hull of \(\operatorname{supp}h\), hence compactly inside \(I\). The homogeneous equation has only combinations of \(e^{x/2}\) and \(e^{-x/2}\), none compactly supported except zero. This proves uniqueness. Reflection and conjugation commute with the equation, so uniqueness proves the last assertion. QED. [ABSTRACT][PAPER]

This gives a full parameter space, not just the observer's one bump. It does not supply a sign. In particular a putative subclass defined by an exact open Fourier gap would be zero: the Fourier transform of a compact smooth nonzero function is entire and cannot vanish on an open interval. A finite-codimension condition or a quantitative frequency-concentration estimate is different and would need its own proof.

## 2. Q1(a): exact mixed form, explicit kernel, and the first missing inequality

### 2.1 Operator construction with all projections retained

Let \(P_0=\mathsf S_{\infty,1}\), \(\mathscr H_0=\operatorname{ran}P_0\), and

\[
 B=I-rU_a,\quad
 G=P_0B^*BP_0\big|_{\mathscr H_0},\quad
 (1-r)^2I\le G\le(1+r)^2I.
\]

The source-faithful semilocal projection is

\[
 \mathsf S_2=BP_0G^{-1}P_0B^*.
 \tag{3}
\]

It is the orthogonal projection onto \(B\mathscr H_0\): \(V=BP_0G^{-1/2}\) is an isometry from \(\mathscr H_0\), so \(VV^*=\mathsf S_2\). This is the finite-Euler Sonin isomorphism of [CCM23] with its metric correction, not a unitary replacement of \(B\). Smooth-test Hilbert--Schmidt and trace domains are those proved in [ST], Theorem 4; no bare angle trace is taken here. [ABSTRACT][PAPER]

### 2.2 The proposed substitution gives a variance, not a sign

**Lemma 2.** For \(Z=T_h\mathsf S_2\),

\[
 \nu_a=\frac{1}{rH}
       \left(\|Z\|_{HS}^2-\Re\langle Z,BZ\rangle_{HS}\right),
 \tag{4}
\]

\[
 n_0-\nu_a
 =\frac{\|(I-U_a)Z\|_{HS}^2}{2H}
 =\frac{\|BZ\|_{HS}^2-(1-r)^2\|Z\|_{HS}^2}{2rH}.
 \tag{5}
\]

**Proof.** Unitary invariance identifies the real mixed inner product of the two half-shifts with \(\Re\langle Z,U_aZ\rangle_{HS}\). Substitute \(U_a=(I-B)/r\). Expanding the squares in (5) and \(B^*B=(1+r^2)I-r(U_a+U_a^*)\) proves the formulas. All factors act on the output of the same Hilbert--Schmidt operator. No commutation with \(P_0\) or \(G\) is used. QED. [ABSTRACT][PAPER]

The available norm bounds imply only \(0\le n_0-\nu_a\le2n_0\). They supply no comparison with \(A_0+J_a+w\). Thus the substitution suggested in the request is exact, but does not by itself resolve (8).

### 2.3 A quadratic kernel determined by archimedean angle data

Here is an explicit spectral construction; it is not an assertion of a finite elementary formula. In physical coordinates take the cosine involution

\[
 (\mathscr F_\infty f)(u)=2\int_0^\infty\cos(2\pi uv)f(v)\,dv.
\]

Let \(J:L^2(0,1)\to L^2(0,\infty)\) be zero extension, \(C=J^*\mathscr F_\infty J\), and \(V_0(f,g)=Jf+\mathscr F_\infty Jg\). Then

\[
 P_0=I-V_0
 \begin{pmatrix}I&C\\C&I\end{pmatrix}^{-1}V_0^*.
 \tag{6}
\]

**Proof.** The Gram operator of \(V_0\) is the displayed block matrix. The compact cosine compression has norm less than 1: norm attainment at 1 would produce a nonzero function and its Fourier transform both compactly supported, contradicting the entire-function uniqueness argument. Hence this Gram operator is invertible, and the subtracted operator is the orthogonal projection onto the closed sum of the two cutoff ranges. Its complement is exactly Sonin's common-kernel space. QED. [ABSTRACT][PAPER]

If \(C\phi_j=\alpha_j\phi_j\), the complement is equivalently resolved by

\[
 e_j^\pm=\frac{J\phi_j\pm\mathscr F_\infty J\phi_j}
                    {\sqrt{2(1\pm\alpha_j)}},\qquad
 P_0=I-\sum_{j,\pm}|e_j^\pm\rangle\langle e_j^\pm|,
 \tag{7}
\]

with strong convergence. This is the explicit archimedean angle data of [CC20]; the physical-to-log unitary is \(f(u)\mapsto e^{x/2}f(e^x)\).

Choose any orthonormal basis \((b_j)\) of \(\mathscr H_0\), and set

\[
 \Phi_j=BP_0G^{-1/2}b_j,\qquad
 k_2(\xi)=\sum_j|\mathcal F\Phi_j(\xi)|^2.
 \tag{8a}
\]

**Lemma 3 (explicit mixed spectral kernel).** The nonnegative density \(k_2\) is locally integrable, independent almost everywhere of the chosen basis, and

\[
 n_2(h)=\int_{\mathbb R}|\widehat h(\xi)|^2k_2(\xi)\,d\xi,
\]

\[
 \boxed{\nu_a(h)=\frac1H\int_{\mathbb R}
            \cos(a\xi)|\widehat h(\xi)|^2 k_2(\xi)\,d\xi,}
 \tag{8b}
\]

\[
 \boxed{n_0-\nu_a=\frac1H\int_{\mathbb R}
       (1-\cos(a\xi))|\widehat h(\xi)|^2k_2(\xi)\,d\xi.}
 \tag{8c}
\]

**Proof.** The \(\Phi_j\) are an orthonormal basis of \(\operatorname{ran}\mathsf S_2\). Sum Parseval's identity for \(T_h\Phi_j\) and use Tonelli. The sum is finite for smooth compact \(h\) by the tested Hilbert--Schmidt theorem. On any fixed frequency compact, choose a sufficiently narrow smooth bump whose Fourier transform is bounded below there; its finite trace proves local integrability of \(k_2\). Basis independence is also pointwise almost everywhere: under a unitary change of countable basis, the sequence of Fourier values transforms by that unitary, initially in local square-integrable sums and then almost everywhere. Shifting the output multiplies these Fourier values by unimodular exponentials; taking the real mixed product gives the cosine. Absolute integrability of (8b) follows from the first formula. QED. [ABSTRACT][PAPER]

Equations (3), (6)--(8) specify a kernel from fixed cosine/prolate data and the Euler multiplier, rather than from unknown zeta zeros. No regularity or pointwise series for the untested semilocal angle distribution is assumed. This answers the kernel request positively in a spectral, quadrature-with-tails sense; it does **not** evaluate the kernel in finite exact arithmetic.

### 2.4 One-sided approximation without cancellation of rounded traces

Put

\[
 A=\tfrac12P_0(U_a+U_{-a})P_0\big|_{\mathscr H_0},\quad
 q=\frac{2r}{1+r^2},\quad
 R_d=\frac1{1+r^2}\sum_{j=0}^{2d+1}q^j A^j,
 \quad \epsilon_d=\frac{q^{2d+2}}{(1-r)^2}.
\]

Since \(\|A\|\le1\), scalar functional calculus gives

\[
 0\le G^{-1}-R_d\le\epsilon_dI.
 \tag{9}
\]

Indeed the remainder at \(x\in[-1,1]\) is
\((1+r^2)^{-1}(qx)^{2d+2}/(1-qx)\); it is nonnegative and at most \(\epsilon_d\). In particular \(R_d\) is positive.

For \(C_h=T_hBP_0\big|_{\mathscr H_0}\) and
\(D_h=(I-U_a)C_h/\sqrt2\), define

\[
 t_d(h)=\operatorname{Tr}(D_hR_dD_h^*),\qquad
 m_D(h)=\|D_h\|_{HS}^2.
\]

Equation (3) and trace cyclicity yield

\[
 \boxed{\frac{t_d(h)}H\le n_0-\nu_a
       \le\frac{t_d(h)+\epsilon_dm_D(h)}H.}
 \tag{10}
\]

For the mixed term alone, replacing \(G^{-1}\) by \(R_d\) in
\(H\nu_a=\Re\operatorname{Tr}(G^{-1}C_h^*U_a C_h)\)
has absolute error at most \(\epsilon_d\|C_h\|_{HS}^2\), by the trace-ideal Cauchy--Schwarz inequality. But (10) is preferable: the minus-phase cancellation is performed **before** certification. QED. [ABSTRACT][PAPER]

For a real-even input the first sufficient inequality not proved here is

\[
 t_d(h)+\epsilon_dm_D(h)
 \le \mathcal D(h)-c_AH+HJ_a(h)+wH,
 \qquad h\in\mathcal H_{00}(I),\ h\text{ real even}.
 \tag{11}
\]

The required statement is (8), not necessarily (11) for one fixed \(d\). The inverse error can be made arbitrarily small for each test, but this observation supplies no uniform sign.

For the full complex class there is a single exact remainder. Define

\[
 q_\infty(\xi)=2\int_0^\infty
     a_\infty(t)(1-\cos(\xi t))\,dt-c_A,
 \qquad a_\infty(t)=\frac{e^{-t/2}}{1-e^{-2t}}.
\]

Then (8c), Plancherel and the exact prime-2 correlation give

\[
 \boxed{\mathfrak m(h):=L_2(v_-)-n_2(v_-)
 =w+\frac1H\int_{\mathbb R}(1-\cos(a\xi))|\widehat h(\xi)|^2
       \left(\frac{q_\infty(\xi)}{2\pi}-k_2(\xi)\right)d\xi
 \ \ge 0.}
 \tag{12}
\]

The equality is proved; the final inequality is **the first unresolved sign**. Its domain is precisely \(\mathcal H_{00}(I)\setminus\{0\}\), its budget is the fixed \(w\), and its source kernel is (6)--(8), not a freely chosen error. No pointwise ordering of its multiplier is claimed. Such ordering would be stronger than the compact pole-null class requires. [ABSTRACT][PAPER for equality; CONDITIONAL for inequality]

### 2.5 Two concrete failed shortcuts

**Compression does not commute with inversion.** In \(\mathbb C^2\), take \(U=\operatorname{diag}(1,-1)\), \(e=(1,1)/\sqrt2\), \(P_0=|e\rangle\langle e|\), and \(B=I-rU\). Then

\[
 G=(3/2)I_{\operatorname{ran}P_0},\quad G^{-1}=(2/3)I,
 \quad P_0(B^*B)^{-1}P_0=6I.
 \tag{13}
\]

The last equality is
\(\tfrac12((1-r)^{-2}+(1+r)^{-2})=6\).
Even with \(T_h\) replaced by a commuting identity operator, removing the projections gives a factor-nine error. This exact plant refutes the proposed general cancellation, not (8) for the source Sonin space. [ABSTRACT][PAPER]

**The positive \(J_a\) series is not a statement for every \(h\).** For arbitrary complex \(h\), its series contains
\(\Re(M_h(\beta)\overline{M_h(-\beta)})\), where
\(M_h(\beta)=\int h(x)e^{\beta x}dx\).
For real odd \(h\) this is \(-|M_h(\beta)|^2\). Choose an even nonnegative nonzero bump \(\eta\) and \(h=(\partial^2-1/4)\eta'\). Lemma 1 makes it pole-null; its moment at \(\beta=5/2\) is nonzero. Thus \(J_a(h)<0\). This does not contradict the correctly scoped real-even formula in [ST]; it prevents using that formula to certify the full complex class. [ABSTRACT][PAPER]

### 2.6 A second exact expression: only the cutoff leakage changes the Sonin trace

There is a useful additional identity, rather than another assumed comparison. For a smooth compact test \(v\), put \(K_v=T_v^*T_v\) and \(Q_0=I-P_0\). Then

\[
 \boxed{n_2(v)-n_\infty(v)
 =-r\Re\operatorname{Tr}_{\mathscr H_0}
 \left[G^{-1}P_0(U_a+U_{-a})Q_0K_vP_0\right].}
 \tag{13a}
\]

**Proof.** The tested trace identities give
\(n_2(v)=\operatorname{Tr}(G^{-1}P_0B^*K_vBP_0)\).
Since convolution commutes with shifts, \(B^*K_vB=B^*BK_v\).
Insert \(P_0+Q_0\) between \(B^*B\) and \(K_v\). The \(P_0\) part cancels exactly against \(G^{-1}\) and gives \(\operatorname{Tr}(P_0K_vP_0)=n_\infty(v)\). The other part uses
\(P_0B^*BQ_0=-rP_0(U_a+U_{-a})Q_0\).
This proves (13a). These manipulations concern tested trace-class operators: in particular [ST], Theorem 4 gives \(T_vP_0\) trace class for smooth compact \(v\), so the remaining products are legitimate. QED. [ABSTRACT][PAPER]

Writing \(e_\infty(v)=n_\infty(v)-L_\infty(v)\), the normalized minus-phase target is exactly

\[
 e_\infty(v_-)-r\Re\operatorname{Tr}
 \left[G^{-1}P_0(U_a+U_{-a})Q_0K_{v_-}P_0\right]\le w.
 \tag{13b}
\]

Thus the new prime does not merely contribute the known scalar \(w\): its Sonin compression also contributes a **cutoff-leakage pairing**. That pairing is source-defined and potentially measurable by an independent implementation. No sign for it has been derived here.

The lack of an automatic sign is real at the operator-algebra level. In the model of (13), choose \(K=\operatorname{diag}(k_1,k_2)\ge0\), which commutes with \(U\) and \(B\). Direct substitution gives
\[
 n_2-n_\infty=\frac{2r}{3}(k_2-k_1).
\]
It takes both signs. Consequently positivity of the multiplier, commutation with \(B\), and positivity of \(G\) do not by themselves control the new mixed term. This is an exact plant against that general algebraic shortcut, not a counterexample for literal Sonin data.

## 3. Q1(b): what the Jacobi paper supplies, and a runnable finite specification

### 3.1 The proof has not become a finite calculation for the entire class

Neither \(k_2\ge0\), the two-sided bounds for \(G\), nor the elementary variance identity compares the weighted density in (12) to zero on every admissible test. The observed margin near 0.34 is one reported test value, not an enclosure for (12). The large-cutoff high-modulation theorem in [SS] changes the cutoff and concerns a finite-dimensional packet; it is not an infinite-dimensional subclass theorem at cutoff 1.

A finite matrix can certify a declared finite-dimensional packet. To infer the entire class from one such matrix still requires an independently proved tail/complement inequality, including its coupling to the packet. No such complement estimate is supplied here. This is the exact remaining analytic obligation, not a claim of impossibility. [ABSTRACT][CONDITIONAL]

### 3.2 The q-series Jacobi matrix is not \(G\)

[CCM24] represents multiplication by the real spectral variable in the cyclic space associated to the local-factor measure. For one prime that measure has, up to its stated scalar normalization, density

\[
 \frac{|\Gamma(1/4+is/2)|^2}{|1-p^{-1/2-is}|^2}\,ds.
 \tag{14}
\]

It is positive on the full real line. Its Jacobi operator is unbounded with real-line spectrum; symmetry gives zero diagonal. Already the compression to the first two orthogonal polynomials is

\[
 \begin{pmatrix}0&a_0\\a_0&0\end{pmatrix},\qquad a_0>0,
\]

and has a strictly negative direction. By contrast, our \(G\) is bounded and satisfies \(G\ge(1-r)^2I>0\). This proves that the literal identification, including a unitary equivalence respecting the operators, is false. A relation through a new function of the Jacobi operator and a specified projection is not excluded, but no such relation is provided by C3. [ABSTRACT][PAPER]

The integrality result is about coefficients of formal power-series expansions. It does not state that all evaluated moments, the Sonin cutoff projection, \(G^{-1}\), or traces for an arbitrary smooth bump lie in \(\mathbb Z[1/\sqrt2]\). The common Euler factor in (14) is a common input, not a proof that two compressed operators coincide. Thus this paper does not remove the carrier or quadrature error of the A/B implementations by an exact-arithmetic substitution.

### 3.3 Finite packet specification; no run performed

The following is one reproducible **prospective** packet, not a relabeling of the observer's bump. Fix \(\sigma=\delta/2\), so that the closed bump support is strictly inside \(I\), and put

\[
 \eta(x)=\begin{cases}\exp(-1/(1-(x/\sigma)^2)),&|x|<\sigma,\\0,&|x|\ge\sigma,\end{cases}
 \quad h_j=(\partial^2-1/4)(x^j\eta(x)),\quad v_j=\mathsf Ah_j.
 \tag{15}
\]

Start with \(j=0,2\) for the real-even slice; use \(j=0,1\) for a full-complex two-generator control. Do not infer a result for all smooth inputs from either packet. Lemma 1 proves pole-nullness exactly, so a numerically small pole integral is only a calibration check.

For a fixed list \(j_1,\ldots,j_k\), compute the following Hermitian coefficient matrices, without normalizing individual rows in different norms:

\[
 \mathbf L_{ij}=L_2(v_i,v_j),\quad
 C_j=T_{v_j}BP_0|_{\mathscr H_0},\quad
 \mathbf M_{ij}=\operatorname{Tr}(C_i^*C_j),\quad
 (\mathbf N_d)_{ij}=\operatorname{Tr}(R_d C_i^*C_j).
 \tag{16}
\]

Here \(L_2(\ ,\ )\) is the Hermitian polarization of the exact source formula, antilinear in its first slot. The operator inequality (9) proves

\[
 \mathbf N_d\preceq\mathbf N\preceq
 \mathbf N_d+\epsilon_d\mathbf M,
 \quad \mathbf N_{ij}=\operatorname{Tr}(G^{-1}C_i^*C_j).
 \tag{17}
\]

**Required implementation inputs and error separation.**

1. Compute the archimedean cosine compression on \((0,1)\) and construct (6), or use a separately certified version of the same Sonin projection. Record the physical/log unitary and both cutoffs. A polar-corrected surrogate with no source error bound is not admissible.
2. Obtain an orthogonal finite-rank projection \(F_M\) on \(\mathscr H_0\). Compute the full-operator moments \(F_M A^j F_M\), \(0\le j\le2d+1\), with enclosures. **Do not replace them silently by \((F_MAF_M)^j\)**. Their difference is a separate Krylov-leakage error; intermediate powers can leave and return to the retained range.
3. Bound, for every coefficient vector \(c\) with \(\|c\|_2=1\),
\[
 \|C_c\|_{HS}^2\le m_*,\qquad
 \|C_c(I-F_M)\|_{HS}\le\tau_M,
 \quad C_c=\sum c_jC_j.
\]
Then either \(G^{-1}\) or \(R_d\) sandwich replacement costs at most
\[
 \delta_{\rm car}=(1-r)^{-2}(2\sqrt{m_*}\tau_M+\tau_M^2).
 \tag{18}
\]
This follows by expanding \(C_c=C_cF_M+C_c(I-F_M)\) and applying the Hilbert--Schmidt Cauchy--Schwarz inequality. It controls all mixed entries as a coefficient-norm bound, not just their diagonals. The tail has an exact independent evaluator: for an orthonormal basis \(e_1,\ldots,e_M\) of the retained range, put
\[
 (\mathbf H_M)_{ij}=\sum_{\ell=1}^M
       \langle C_i e_\ell,C_j e_\ell\rangle.
\]
Then \(\|C_c(I-F_M)\|_{HS}^2=c^*(\mathbf M-\mathbf H_M)c\). Thus an upper enclosure of \(\mathbf M-\mathbf H_M\) supplies \(\tau_M^2\); the total matrix \(\mathbf M\) is the polarized archimedean Sonin trace of \(Bv_j\), evaluable through [CC20]'s tested prolate expansion. This still needs its own rigorous series and quadrature remainder; it is not an exact number obtained from a guessed finite carrier.
4. Add certified quadrature, source-projection, moment-power and rounding errors. The inverse tail \(\epsilon_d\mathbf M\) is its own one-sided addend and does not cover these other errors. For the archimedean integral at zero, use the smooth autocorrelation/difference cancellation, not separate divergent integrals. At infinity use the explicit exponential density tail.
5. If coordinates are orthonormalized, carry the exact or interval-enclosed positive coefficient Gram matrix through the congruence. Otherwise certify in the stated Euclidean coefficient norm and do not label the error a physical \(L^2\) bound.

For example, if the computed matrices have norm errors \(\delta_L,\delta_N,\delta_M\), including the carrier contributions, the sufficient lower matrix is

\[
 \mathbf C_{\rm low}=
 \widehat{\mathbf L}-\widehat{\mathbf N_d}
 -\epsilon_d\widehat{\mathbf M}
 -(\delta_L+\delta_N+\epsilon_d\delta_M)I.
 \tag{19}
\]

A certified \(\mathbf C_{\rm low}\succeq0\) proves (R1−) on that packet, including all complex coefficient combinations. A strict negative **upper** bound for
\(c^*(\mathbf L-\mathbf N_d)c\), with all errors included, proves a counterexample, since \(\mathbf N\succeq\mathbf N_d\). A negative lower bound alone proves nothing. A zero-straddling enclosure remains inconclusive.

The output should contain the exact list (15), \(d,M\), the inverse tail, every independent error, the coefficient Gram, both sign enclosures and a witness vector if the upper enclosure is negative. Increasing \(M\) without a certified \(\tau_M\) is not completion of this specification. No universal finite stopping bound is asserted. [FINITE_CELL][CONDITIONAL until evaluated; equations (17)--(19): ABSTRACT/PAPER]

## 4. Q1(c): both plants and the limits of an identifying claim

### 4.1 The specified false local factor

Keep the Sonin projection fixed, as the parent plant explicitly requires, and multiply the arithmetic object by

\[
 M_2(s)=(1-2^{3/4-s})(1-2^{-1/4+s}).
\]

Its explicit off-line zero lattices give, by Poisson summation,

\[
 Q_M(v)=2a\|v\|^2+4a\sum_{j\ge1}\cosh(ja/4)C_v(ja).
\]

For normalized \(v_-\), only \(j=1\) survives, so

\[
 Q_M(v_-)=-\delta_M,\quad
 \delta_M=2a(\cosh(a/4)-1)>0,\qquad
 \mathfrak m_\sharp(h)=\mathfrak m(h)-\delta_M.
 \tag{20}
\]

This is an exact evaluation, not a simulation. It checks the sign and the missing contact term: omitting the \(2a\) diagonal gives a different plant. A proof of \(\mathfrak m\ge0\) alone would **not** establish survival. A proof of \(\mathfrak m\ge\delta_M\) on a specified subclass would. The reported margin near 0.34 suggests survival of that one diagnostic row, but no certified lower bound for it is supplied. We therefore do not score survival for the whole class. [ABSTRACT][PAPER]

Survival does not logically imply a purely archimedean proof. An arithmetic inequality can be robust under one bounded arithmetic perturbation. The inference in Q1(c) is too strong.

There is a useful exact stress test of this point. Choose a prime \(p\) with \(\log p>a+2\delta\), and use the analogous false factor \(M_p\), still keeping the original Sonin object fixed. Every nonzero shifted autocorrelation of this factor lies outside the test support, and hence

\[
 Q_{M_p}(v)=2\log p\,\|v\|^2>0\quad(v\ne0).
 \tag{21}
\]

Thus any minorant on this fixed short class, if proved for the original source, survives this different off-line-zero plant. This establishes a **restricted-class detection limitation**, not falsity of the zeta minorant and not existence of a new local-field Sonin model. A fixed short test class cannot by itself certify all zeros of every perturbed global function. Its possible extension to an exhausting collection is an additional question.

### 4.2 Davenport--Heilbronn

[AF] Section 1.4 discusses robustness of its counting method, including non-Euler-product examples. That statement does not supply a Davenport--Heilbronn analogue of (3). Our particular construction uses the factorized local Fourier/scattering multipliers and the bounded finite Euler map \(B\). A linear combination of Dirichlet \(L\)-functions does not acquire that map merely by sharing a functional equation or a gamma factor. [ABSTRACT][PAPER/source audit]

Consequently the requested **native** split \(N_{DH,S}-E_{DH,S}\), with the same specified local construction, is **not established by the supplied sources**. Neither the sign nor the failure of its analogue of (8) is presently defined by this dictionary. It would be tautological, not a crosswalk, to set \(E_{DH}=N_\zeta-Q_{DH}\) after choosing an unrelated positive \(N_\zeta\).

This is not a theorem that no Sonin-type model for a Davenport--Heilbronn function can exist. Nor does an off-line zero force every short-window restricted inequality to fail. The plant returns **OBJECT_CROSSWALK_MISSING**, not a fabricated positive or negative value. The observer's composite DH prediction remains unresolved.

### 4.3 The finite-stencil obstruction has a different test quantifier

`NoFiniteStencilMinorant` forbids fixed nonnegative finite-stencil minorants imposed on the full compact profile class using cutoffs of every rational translate of a radical vector. The current class has fixed small support and a two-lobe relation; those witnesses are not shown to belong to it. Therefore the assertion that **any** proof of (8) must be nonlocal does not follow from that theorem. Our kernel representation is nonlocal, but we do not exclude other restricted-class mechanisms without a new argument. [ABSTRACT][PAPER]

## 5. Q1(d): the next prime and the exact mixed-prime obligation

Let \(b=\log3\), \(r_3=3^{-1/2}\). At the same cutoff 1 set

\[
 B_{23}=(I-rU_a)(I-r_3U_b),\quad
 G_{23}=P_0B_{23}^*B_{23}P_0|_{\mathscr H_0},\quad
 \mathsf S_{23}=B_{23}P_0G_{23}^{-1}P_0B_{23}^*.
 \tag{22}
\]

Its independent Gram bounds are
\(\prod_{p=2,3}(1-p^{-1/2})^2I\le G_{23}\le
\prod_{p=2,3}(1+p^{-1/2})^2I\).
The source statement for pole-null tests of diameter at most \(\log5\) is

\[
 n_{23}(v)\le L_{23}(v),\quad
 L_{23}(v)=\mathcal D(v)-c_A\|v\|^2
   -2w_2C_v(a)-2w_3C_v(b)-2w_4C_v(2a),
\]

\[
 w_2=a/\sqrt2,\quad w_3=b/\sqrt3,\quad w_4=a/2.
 \tag{23}
\]

**The prime power 4 cannot be omitted.** At the endpoint \(\log5\) the smooth autocorrelation vanishes; otherwise use strict support diameter. For the particular three-lobe family below, \(b+2\delta<\log4\), so the 4 term happens to vanish there, not in the full window class. [ABSTRACT][PAPER]

Take a real-even \(h\in\mathcal H_{00}(I)\) and centers \(c_0=0,c_1=a,c_2=b\). Set \(v_z=\sum_{i=0}^2z_iU_{c_i}h\). The translated supports are disjoint. Define \(n_0^{23}\) and \(\nu_d^{23}\) by the formulas in Section 2 with \(\mathsf S_{23}\), and define \(J_d(h)\) by the shifted archimedean correlation formula. Put

\[
 d_0=A_0-n_0^{23},\quad
 d_{01}=-J_a-w_2-\nu_a^{23},\quad
 d_{02}=-J_b-w_3-\nu_b^{23},\quad
 d_{12}=-J_{b-a}-\nu_{b-a}^{23}.
 \tag{24}
\]

Then direct polarization gives

\[
 L_{23}(v_z)-n_{23}(v_z)=H z^*D z,
 \quad D_{ii}=d_0,\quad D_{ij}=d_{ij}\ (i<j),\quad D_{ji}=\overline{D_{ij}}.
 \tag{25}
\]

All the displayed entries are real on this real-even slice. The distance \(b-a=\log(3/2)\) has no prime atom; it still has both an archimedean and a Sonin mixed term. The separation from the other atom distances exceeds the lobe-correlation width \(2\delta\), justifying the exact weights in (24). The general complex case uses the polarized complex mixed forms instead of replacing them by their real parts.

For the natural difference-generated three-lobe class \(z_0+z_1+z_2=0\), use columns \((-1,1,0)^T,(-1,0,1)^T\) of \(R\). Its exact requirement is

\[
 R^*DR=\begin{pmatrix}
 2(d_0-d_{01})&d_0-d_{01}-d_{02}+d_{12}\\
 d_0-d_{01}-d_{02}+d_{12}&2(d_0-d_{02})
 \end{pmatrix}\succeq0.
 \tag{26}
\]

Besides the two two-lobe diagonal inequalities, this requires

\[
 |d_0-d_{01}-d_{02}+d_{12}|^2
 \le4(d_0-d_{01})(d_0-d_{02}).
 \tag{27}
\]

The necessity of a mixed condition is not cosmetic: \(\left(\begin{smallmatrix}1&2\\2&1\end{smallmatrix}\right)\) has positive diagonal but value \(-2\) on \((1,-1)\). This is an exact plant for diagonal-only certification, not a counterexample to the source matrix (26).

Two things change before any Hardy--Littlewood question arises: adding prime 3 changes **the entire Sonin projection**, so the old \(n_0,\nu_a\) cannot be reused, and combining the two lobe differences requires (27). For a fixed set \(\{2,3\}\) these are operator integrals involving fixed shifts, not an asymptotic average over prime pairs. There is no demonstrated identification with the long-Dirichlet-polynomial prime-pair obstruction of [AF]. Which actual entry fails, if any, has not been computed or proved. [ABSTRACT][PAPER for identities; CONDITIONAL for sign]

## 6. Q2(a): the correct dictionary is a tensor square, not one Weil value

### 6.1 Separate the three kinds of window

In the dated primary PDF [AF], put

\[
 L=\log(T/(2\pi)),\quad X=e^L,\quad
 \phi(x)=\chi(L/2+x)\chi(L/2-x)\sqrt{\psi(x/L)},
\]

\[
 \alpha_k=T+2\pi k/L,\quad
 u_k(x)=e^{i\alpha_kx}\phi(x),\quad
 a_\psi=\|\phi\|_2^2/L,\quad s_\psi=(a_\psi L^2)^{-1}.
 \tag{28}
\]

Use the paper's endpoint smoothing \(\chi\) and admissible nonnegative window \(\psi\). The latter lives on the normalized interval \([-1/2,1/2]\), **not** on \([T,2T]\). The functions \(u_k\) live in log space on an interval of length \(L\). The interval near \([T,2T]\) is a zero-height/modulation selection. Their covariance autocorrelations have support diameter at most \(L\), so only \(n\le X\) enter the prime side.

Let \(\mathbf W_{ij}=\mathcal B(u_i,u_j)\) for the full Weil form. With the paper's normalization, the source identity is

\[
 \widetilde G+\widetilde E_{\rm height}=s_\psi\mathbf W.
 \tag{29}
\]

\(\widetilde G\) omits zero heights outside the enlarged height interval; its height-tail matrix is not the Sonin angle error. Dropping it changes an exact identity to an asymptotic statement requiring the paper's separate estimate. [ABSTRACT][PAPER/source dictionary]

### 6.2 Exact two-copy formula

On the algebraic tensor product of the test space and its conjugate, define the tensor sesquilinear form \(\mathcal B\otimes\overline{\mathcal B}\). For

\[
 F=\sum_{k=0}^{d-1}u_k\otimes\overline{u_k},
\]

one has

\[
 \boxed{\|\mathbf W\|_{HS}^2
       =(\mathcal B\otimes\overline{\mathcal B})(F,F).}
 \tag{30}
\]

**Proof.** Expanding the right side yields
\(\sum_{i,j}\mathcal B(u_i,u_j)\overline{\mathcal B(u_i,u_j)}\).
This is the Hilbert--Schmidt square, without any assumption on the sign of \(\mathcal B\). No completion or infinite trace is required for this finite algebraic identity. QED. [FINITE_CELL][PAPER]

Accordingly the source-square quantity is degree two in the source form, with two prime sums after expansion. It is not the degree-one functional \(\mathcal Q(v)\) on a test built independently of that source. Subtracting a linear trace or dimension term from it does not remove its quadratic part.

### 6.3 Exact falsifier for the proposed one-copy identity

Fix the test geometry and a family of Hermitian sources
\(W_t=\operatorname{diag}(1,t)\) on \(\mathbb C^2\). Then

\[
 \|W_t\|_{HS}^2=1+t^2,\qquad
 W_t(v,v)=|v_1|^2+t|v_2|^2.
\]

For a fixed window-built \(v\), the centered second difference in \(t\) is \(2s^2\) on the first expression and zero on the second. They cannot be identical. More generally, for a source perturbation \(W+tA\),

\[
 \|W+sA\|_{HS}^2+\|W-sA\|_{HS}^2-2\|W\|_{HS}^2
 =2s^2\|A\|_{HS}^2.
 \tag{31}
\]

This refutes a **source-linear, window-only crosswalk**, not every logically possible nonlinear selection of a test for one fixed scalar value. Choosing the amplitude of a test using the desired Hilbert--Schmidt square would merely encode the answer and supplies no estimate. A new source-specific nonlinear identity is not ruled out by this plant, but none is supplied by [AF] or the Sonin split. This scope is why Q2 as a whole remains partial rather than declaring all relations impossible. [ABSTRACT][PAPER]

The source-side double-integral representation in [AF] is consistent with (30): its integrand contains the square of the reproducing/modulation kernel and **two** copies of the geometric Weil distribution. This is exactly where products \(\Lambda(n)\Lambda(m)\) enter; they are not an extra term of a single linear Weil value.

### 6.4 Lamzouri's notation and the word mollifier

[L26] uses the Fourier convention with \(2\pi\). Under \(x=Lu\), its centered zero variable is \(-L\gamma_\rho/(2\pi)\), where \(\gamma_\rho=(\rho-1/2)/i\). Reflection may be suppressed for even windows only after stating it. Its kernel is the Fourier transform of \(\eta^2\); its \(Q_\delta=\eta^2*\eta^2\) is a test **function**, not our quadratic functional \(\mathcal Q\).

In particular, the removal of \(w(\rho-\rho')=4/(4-(\rho-\rho')^2)\) is the two-test identity

\[
 r_{\delta,T}=Q_\delta-\frac{Q_\delta''}{4(\log T)^2},\quad
 \widehat r_{\delta,T}(z)=
 \left(1+\frac{\pi^2z^2}{(\log T)^2}\right)\widehat Q_\delta(z).
 \tag{32}
\]

The factor equals \(w^{-1}\) in the stated rescaled variable. It is not a Sonin projection or a positive inverse-Gram estimate. The fixed-test pair-correlation estimates must be applied separately before taking this \(T\)-dependent linear combination. No classical mollifier residual is thereby identified with \(E_S\). [ABSTRACT][PAPER/source dictionary]

## 7. Q2(b): the semilocal matrix split does apply, but not as proposed

For a fixed finite set of primes containing all \(p\le X\), polarize the same tested identity used in [ST]. Let

\[
 (\mathbf N_S)_{ij}=\operatorname{Tr}(T_{u_i}^*T_{u_j}\mathsf S_S),
 \quad (\mathbf E_S)_{ij}=e_S(u_i,u_j),
\]

\[
 \mathbf\Pi_{ij}=
 \overline{A_+(u_i)}A_-(u_j)+\overline{A_-(u_i)}A_+(u_j).
\]

At equal cutoffs 1 the contact term is zero. The exact matrix equation is

\[
 \boxed{\mathbf W=\mathbf N_S-\mathbf E_S+\mathbf\Pi,\qquad
 \widetilde G=s_\psi(\mathbf N_S-\mathbf E_S+\mathbf\Pi)
                  -\widetilde E_{\rm height}.}
 \tag{33}
\]

**Proof.** The source identity on autocorrelation tests gives each diagonal quadratic value. Polarization gives the off-diagonal entries. The support restriction deletes precisely the primes not appearing in the finite geometric sum. The modulated windows are not assumed pole-null, so their rank-at-most-two pole matrix is retained. Equation (29) supplies the separate height tail. QED. [FINITE_CELL][PAPER]

If primes between \(X\) and \(T\) are added, their direct source evaluations vanish on these supports, but both Sonin and angle pieces can change and must cancel in the difference. Thus even the choice \(S=\{p\le T\}\) does not identify their separate entries with those for \(S=\{p\le X\}\).

Already before the height correction,

\[
\begin{aligned}
 \|\mathbf N-\mathbf E+\mathbf\Pi\|_{HS}^2
 =&\|\mathbf N\|_{HS}^2+\|\mathbf E\|_{HS}^2+\|\mathbf\Pi\|_{HS}^2
 -2\Re\operatorname{Tr}(\mathbf N^*\mathbf E)\\
 &+2\Re\operatorname{Tr}(\mathbf N^*\mathbf\Pi)
 -2\Re\operatorname{Tr}(\mathbf E^*\mathbf\Pi).
\end{aligned}
 \tag{34}
\]

Consequently the off-diagonal prime second moment is not identifiable with one piece of \(\mathbf E\) by the linear split. It is distributed through quadratic and mixed expressions. Positivity of \(\mathbf N\) does not bound these expressions with the sharp counting budget. [FINITE_CELL][PAPER]

### Where the quantitative obligation really reappears

A representative off-diagonal Dirichlet-polynomial expression has factors

\[
 \sum_{n\ne m\le X}\frac{\Lambda(n)\Lambda(m)}{\sqrt{nm}}
 b_n\overline{b_m}\int_T^{2T}e^{it\log(n/m)}dt,
\]

with the specific window weights determined by the source calculation. Direct integration gives

\[
 \left|\int_T^{2T}e^{it\log(n/m)}dt\right|
 \le\min\left(T,\frac{2}{|\log(n/m)|}\right).
 \tag{35}
\]

When \(X\gg T\), pairs with \(|n-m|\) on the scale \(X/T\) need not oscillate away. A sharp asymptotic for that regime requires new control of these weighted correlations. [AF] identifies Hardy--Littlewood-type information as the unavailable input in its extension; it does not prove that every different method must assume the full Hardy--Littlewood conjecture.

The Sonin projector for each finite \(S\) is defined without such a conjecture. What is missing is a **uniform, cancellation-preserving estimate for (34) as the prime set and modulation family grow**, strong enough for the proposed counting remainder. The crude Euler-Gram inverse bounds and a few fixed-prime phase inequalities do not give it. No unconditional control of the beyond-band off-diagonal remainder is proved here. Equally, no theorem that such control logically requires Hardy--Littlewood is proved. The observer's necessity prediction is therefore unresolved, with a clearly located quantitative debt. [COFINAL_FAMILY][CONDITIONAL]

## 8. Q2(c): cheapest decisive check and exact calibration constants

A scalar agreement at one window cannot establish the proposed identity. The cheapest decisive test of the **claimed one-copy representation** is (31): freeze all windows and their normalization, vary one source coefficient affinely, and take the second difference. For the exact control \(W_t=\operatorname{diag}(1,t)\), the outcomes at step \(s=1\) are **2 versus 0**, without a numerical run. In a source evaluator the same test uses its compressed nonzero perturbation matrix \(A\), predicting \(2\|A\|_{HS}^2\) versus zero. This isolates the category error before any costly Sonin computation. [FINITE_CELL][PAPER]

The window constants are useful **normalization controls**, not identifying tests. The functional printed in [AF] is

\[
 R(\psi)=\frac{\int_{-1/2}^{1/2}\psi(u)^2du+
   \int_{-1/2}^{1/2}\!\int_{-1/2}^{1/2}|u-v|\psi(u)\psi(v)dudv}
 {\left(\int_{-1/2}^{1/2}\psi\right)^2}.
 \tag{36}
\]

For \(\psi_0=1\) on this interval, the double integral is \(1/3\), so \(R(\psi_0)=4/3\) exactly.

For \(\psi_{MT}(u)=\cos(\sqrt2u)\), let
\(K\psi(u)=\int_{-1/2}^{1/2}|u-v|\psi(v)dv\).
Inside the interval, \((\psi+K\psi)''=-2\psi+2\psi=0\). Evenness makes this function constant. With \(s=1/\sqrt2\), evaluating at zero gives
\(\psi+K\psi=\cos s+\sin s/\sqrt2\), while \(\int\psi=\sqrt2\sin s\). Therefore

\[
 \boxed{R(\psi_{MT})=\frac12+\frac1{\sqrt2}\cot(1/\sqrt2).}
 \tag{37}
\]

The request has an extra factor \(1/2\) in the cotangent term. Equations (36)--(37) prove the correction directly rather than selecting a decimal that matches a reported proportion. The same constant occurs in [L26], with its own normalized window convention. Endpoint smoothing is handled by the source's limiting estimates; a discontinuous control window is not silently inserted as a compact-smooth theorem input. [ABSTRACT][PAPER]

The comparison to a Sonin machine is legitimate only after that machine constructs exactly the window family (28), the full polarized matrix, its pole correction, height tail and scaling (29). Agreement with 4/3 alone would remain an asymptotic consistency check, not a proof that (30) collapses to one original test.

## 9. Predictions: immutable probabilities and honest outcomes

The following probabilities are those in the request, not revised posterior beliefs. `NOT_DELIVERED` records failure of a prediction about this batch's proof output; it is not a counterexample to the underlying inequality.

| Observer prediction | p | Fate | Reason |
|---|---:|---|---|
| P_8_PROVED_ON_CLASS | 0.20 | REFUTED_AS_BATCH_OUTPUT; SIGN_UNRESOLVED | No proof of (12) for all admissible h was obtained. |
| P_8_PROVED_ON_SUBCLASS | 0.30 | REFUTED_AS_BATCH_OUTPUT; EXISTENCE_UNRESOLVED | No explicit nonzero infinite-dimensional sign subclass at cutoff 1 is proved here. Lemma 1 is a parametrization, not a sign theorem. |
| P_NU_A_HAS_EXPLICIT_KERNEL | 0.55 | CONFIRMED_WITH_SPECIFIED_READING | (6)--(8) give a source-defined spectral quadratic kernel and (9)--(10) its certified-inverse approximation, not a finite elementary evaluation. |
| P_CCM_QSERIES_IS_OUR_GRAM | 0.60 | REFUTED | Positive bounded G versus the indefinite/unbounded Jacobi multiplication operator, Section 3.2. |
| P_DH_PLANT_KILLS_IDENTIFYING_CLAIM | 0.50 | UNRESOLVED | The native DH/Sonin crosswalk and its phase sign are not supplied. A different artificial-factor limitation is proved, but cannot score this event. |
| P_CROSSWALK_A_YES | 0.35 | NOT_ESTABLISHED; SOURCE_LINEAR_VERSION_REFUTED | Exact second-difference plant (31); unrestricted nonlinear existence is not decided. No one-test dictionary is delivered. |
| P_CROSSWALK_B_NEEDS_HL | 0.70 | UNRESOLVED_AS_NECESSITY_CLAIM | The missing long-prime correlation estimate is located; necessity of the full conjecture for Sonin methods is not proved. |

The judge registered the following forecasts in the living chat before the corresponding checks, after reading the request but before the external operator audit. No claim is made that these precede other agents' unobserved work.

| Judge forecast | p | Fate |
|---|---:|---|
| Explicit spectral kernel for nu_a | 0.85 | CONFIRMED, Lemma 3 |
| The q-series Jacobi/G identification fails | 0.90 | CONFIRMED, Section 3.2 |
| The direct HS-square-to-one-Weil-value crosswalk fails | 0.90 | CONFIRMED within the source-linear scope, (31) |
| A full proof of (8) is obtained | 0.15 | REFUTED_AS_BATCH_OUTPUT; no mathematical negation inferred |

These are proof-output predictions, not calibrated probabilities of RH or of the true sign. The supplied B table, its original probabilities and its absence of certified enclosures have not been altered.

## 10. Consumer contract, alternatives, and one directive

### K8A dependency contract

- **DOWNSTREAM_CONSUMER:** the published Weil criterion on all complex compact smooth tests.
- **ACTUAL_CONSUMER_REQUIREMENT:** nonnegativity of the full form on that class, or a proved exhaustive approximation with a vanishing error budget. One fixed two-lobe class is not that consumer.
- **ORIGINAL_REQUESTED_OBJECT:** (R1−) at S={infinity,2}, cutoff 1; and a one-copy identification with a pair-correlation Hilbert--Schmidt residual.
- **ORIGINAL_OBJECT_IS:** `UNKNOWN` as a necessary component of a future exhaustive route. The one-copy identity is `NOT_NECESSARY` for either the restricted sign problem or the known counting argument.
- **KNOWN_WEAKER_INTERFACES:** (19) certifies each declared packet; an exhaustive family with a separately proved complement/recovery budget could then approach the restricted sign problem. Equation (33), not a one-copy identity, is the valid finite-matrix connection. Neither is currently a global supplier.
- **FAILURE_TYPE for the sign:** `NO_DERIVATION`, not a counterexample. **EPISTEMIC_STATUS:** `RESEARCH_DEBT`.
- **REOPEN TRIGGER:** a rigorous lower enclosure for (12) on an explicit class with a full outside-packet estimate; or a strict negative upper enclosure for one literal admissible test. A fresh fit or an inverse tail without a carrier bound is not a trigger.
- **NOVELTY_AXIS:** cancellation-preserving mixed-trace kernel, exact pole-null parametrization, and separation of the one-source and two-source objects. Historical novelty is not claimed.

The three scoped refutations in the header have exact evidence in (13), Section 3.2 and (31). None reaches all admissible proof representations or kills the RH route. In particular no absence-of-source finding is classified as mathematical impossibility.

### Two representations retained, with estimates rather than promises

**R-A: direct minus-kernel certificate.** Use (10), (15)--(19), estimating the whole difference before splitting entries. A certified negative upper margin kills (R1−); a lower matrix proves only the packet. Kill-power estimate 9/10, cost 4/10 for a small packet after the carrier is validated, 8/10 for the whole-class complement estimate. Main risk: the inverse error is cheap while the Sonin carrier error remains unproved.

**R-B: cutoff-leakage and pole-removal representation.** Use (13b) to separate the known archimedean tested trace from the exact noncommuting cutoff term, and the bijection (2) to work on an unconstrained compact \(\eta\)-space. Retain the entire signed kernel before integrating by parts. Derive the actual contact and mixed-shift terms, then seek a finite-rank/complement comparison there. This must not import the archimedean contact coefficient from [CC20] as a semilocal coefficient without proof. Kill-power estimate 8/10, cost 6/10. Main risk: the semilocal kernel's singular/contact contributions at zero and at prime distances have not been separately identified. If a positive direction is found it is a literal test, not a surrogate phase.

Both are changes of representation of the same frozen sign, not new free hypotheses exported to the roof. No expensive computation or formalization is authorized by these cost estimates.

**One directive to the observer:** implement the two-generator finite-packet specification (15)--(19) at the fixed cutoff, first printing all independent error obligations and the exact (31) calibration. Do not rerun the old raw A/B tables. Return a certified lower matrix, a certified negative upper witness, or `CARRIER_OR_COMPLEMENT_ERROR_UNRESOLVED`. Do not report a whole-class theorem from a finite packet, substitute the q-series Jacobi operator, change the cutoff, or drop prime-power/contact/pole terms. This is the single next proposed bounded test; this adjudication itself performs no run.

**DISCRIMINATOR for zero-consistent output:** the interval for
\(\mathfrak m(h)=L_2(v_-)-n_2(v_-)\), or the smallest generalized eigenvalue of the fully error-adjusted packet difference, with exact Gram normalization. Lower endpoint nonnegative proves the stated packet. Upper endpoint strictly negative for a witness refutes the class. Straddling zero is inconclusive and must identify which error addend dominates. A failure of the sufficient lower certificate is not a negative witness.

## 11. Closeout and delivery gate

**What became smaller?** The mixed Sonin quantity is represented by a known spectral density and by the positive difference sandwich (10), so it need not be computed as two separately rounded large traces. The entire pole-null input class has the explicit inverse parametrization of Lemma 1. The next-prime obligation is the concrete mixed determinant (27). The pair-correlation connection has a correct tensor and polarized-matrix dictionary.

**What was refuted?** The literal q-series/Gram identification, the projection-free inverse cancellation, and a source-linear one-test representation of a Hilbert--Schmidt square. The full phase inequality was not refuted.

**What must not recur?** Multiplying an unproved source identification by an exact coefficient ring; replacing a Gram inverse by a compressed full inverse; transferring real-even J positivity to arbitrary complex tests; dropping the height tail or the rank-two poles; interpreting a fixed-prime mixed term as an asymptotic Hardy--Littlewood theorem; promoting a surviving short-window plant to global identification.

**Remaining gap:** the lower bound in (12) on the frozen class, or a genuine infinite-dimensional subclass with its own proved analytic control. A finite packet without a complement theorem does not close it.

```yaml
iteration:
  target: REQ-2026-09-06-PHASEPROOF
  status: OPEN
  progress_class: REPRESENTATION_PROGRESS
  cognitive_operator_used: REPRESENTATION_SHIFT
  failed_strategy: exact_arithmetic_Jacobi_substitution_and_one_copy_HS_crosswalk
  new_gap_name: SEMITABLE_R1_MINUS_AT_FIXED_CUTOFF_1
  invariant_learned: preserve_source_degree_projections_cutoff_and_test_quantifiers
  forbidden_future_move: identify_a_second_source_moment_with_a_single_source_value
  next_decisive_test: certified_two_generator_minus_packet_with_separate_carrier_error
  route_score: 3
```

**Verification handoff.** Only `EXPECTED_VERDICT_PATH` is written, with a `[Proshka]` commit prefix. No Lean file is written, so there is no new axiom profile or kernel gate to claim. The delivery receipt must give the actual returned commit and blob, then verify the document at that commit and the changed-file list. The commit identifier is returned outside its own content to avoid a recursive hash assertion. The branch may advance concurrently; its current head is not mathematical evidence for this pinned review.

This verdict establishes no new all-test lower envelope for the Weil form and makes no RH claim. The mathematical endpoint is a partial proof with the exact unresolved inequality (12), not a renamed completed proof.
