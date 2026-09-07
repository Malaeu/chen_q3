# STATUS: TRY_SIGNED_MEAN_COMPENSATION_WITH_REGIONAL_LOG_ENERGY
```yaml
OPERATIVE_CLASS: TRY_SIGNED_MEAN_COMPENSATION_WITH_REGIONAL_LOG_ENERGY
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-07-INVARIANT
BOUNDARY_ID: GOAL058_THREE_LOBE_CLASS_THEOREM_AND_ALL_N_SIGNED_HEAD_INVARIANT
RESULT:
  OVERALL: PARTIAL_WITH_PRECISE_REMAINDER
  Q1: PARTIAL_WITH_PRECISE_REMAINDER
  Q1a: PROVED_ON_CLASS
  Q1b: PROVED_ON_CLASS
  Q1c: PARTIAL_WITH_PRECISE_REMAINDER
  Q2: PARTIAL_WITH_PRECISE_REMAINDER
  Q2a: OBSTRUCTION_NAMED
  Q2b: PARTIAL_WITH_PRECISE_REMAINDER
  Q2c: OBSTRUCTION_NAMED
  Q2d: COMPUTATION_SPECIFIED
  Q2e: COMPUTATION_SPECIFIED
  Q3: COMPUTATION_SPECIFIED
REQUEST_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  COMMIT: 6f8e791e58a95eb1af4e08c025e8c4bca4902fc1
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_SIGNED_HEAD_INVARIANT_2026-09-07.txt
  GIT_BLOB: 9ccdebb97a8247deb01393b56223d097823d1223
  SHA256: 4ae2d7ae8c3a822d58b817bd6882545197289e8175bb65b3c8656e53abe2a6cc
  BYTES: 15524
  LINES: 77
  FINAL_LF: true
  FETCHED_UTF8_HASHES_AND_COUNTS_RECOMPUTED: true
  ALL_FOUR_CHECKS_MATCH: true
ADDENDUM_LOCK:
  PATH: docs/routeB_bus/INVARIANT_ADDENDUM_THREE_MECHANISMS_2026-09-07.md
  FETCHED_BRANCH: rh_clean
  PINNED_READBACK_COMMIT: da1293a3b5e7a422a9726016b372ed7046a06181
  GIT_BLOB: fc54251f4d5f677844346fd76203bc9a2f92a066
  PRIORITY: [TRANSITION_INVARIANT, COMPENSATION, GRAM_SOS]
  NO_N_DEPENDENT_COMPUTATION_IN_FINAL_PROOF: ACCEPTED
  HARD_SUCCESS_CRITERION_MET: false
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
  THREE_LOBE_TOTAL_POLE_NULL_CLASS_FLOOR: 3/20
  THREE_LOBE_FLOOR_USES_NUMERICAL_PACKET: false
  REGIONAL_LOG_ENERGY_GAP: proved_on_paper
  FREE_MEAN_DIRECTION_RETAINED: true
  PRIME_FORM_ON_EVERY_FREE_MEAN_KERNEL_IS_NONNEGATIVE: false
  FIRST_COUNTEREXAMPLE_TO_THAT_MEAN_CLAIM: four_lobes_at_1_2_3_5
  ISOLATED_PRIME_STAR_MEAN_FORM_NEGATIVE_INDEX_AT_MOST_ONE: true
  THAT_INDEX_STATEMENT_APPLIES_TO_FULL_SIGNED_HEADS: false
  CANONICAL_HEADS_NATURALLY_NESTED: not_established
  DECREASING_EPSILON_GIVES_POSITIVE_INCREMENT: false
  UNIVERSAL_TRANSITION_INVARIANT_PROVED: false
  UNIVERSAL_COMPENSATION_PROVED: false
  UNIVERSAL_GRAM_SOS_PROVED: false
  ALL_N_HEAD_SIGN_PROVED_OR_REFUTED: false
  GLOBAL_CANDIDATE_SCOPE: COFINAL_FAMILY
  GLOBAL_CANDIDATE_VERIFIER: CONDITIONAL
  SELECTED_MECHANISM_AFTER_TRANSITION_AUDIT: SIGNED_COMPENSATION
  SCHUR_HEAD_EQUALS_RAW_ZERO_EVALUATION_GRAM_ON_V_N: false
  FINITE_HEIGHT_ZERO_COUNT_BOUNDS_FULL_HEAD_RANK: false
CLOSES:
  - REQ-2026-09-07-INVARIANT
CLOSED_PAPER_REVIEW_OBLIGATIONS:
  - CHAIN_C22_THREE_LOBE_WHOLE_CLASS_POSITIVE_FLOOR
  - CHAIN_FORM_CORE_SKETCH_EXPANDED
  - ISOLATED_PRIME_STAR_MEAN_RANK_AND_FIRST_SIGN_CHANGE
CLOSES_ANALYTIC_RH_SUPPLIERS: []
OPENS: []
REMAINS_OPEN:
  - ALL_SUPPORT_SIGNED_SCHUR_HEAD_LOWER_BOUND
  - SOURCE_UNIFORM_INNOVATION_OR_COMPENSATION_MECHANISM
SCOPED_REFUTATIONS:
  - NAME: ALL_FREE_CENTER_MEANS_HAVE_NONNEGATIVE_PRIME_FORM
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: exact_negative_prime_form_on_admissible_four_lobe_test
    EVIDENCE: section_3_equation_24
    SCOPE: ABSTRACT
    VERIFIER: PAPER
  - NAME: DECREASING_EPSILON_IS_A_PSD_INCREMENT_AT_FIXED_SPLIT
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: exact_negative_definite_resolvent_difference
    EVIDENCE: section_4_equation_29
    SCOPE: ABSTRACT
    VERIFIER: PAPER
EVIDENCE_BOUNDARY:
  REPOSITORY_MATHEMATICAL_CUTOFF: request_commit
  ADDENDUM_IS_EXPLICITLY_AUTHORIZED_LATER_INPUT: true
  OLD_UPLOADED_ROADMAPS_USED_AS_PREMISES: false
  ALL_SHELF_SHA_PREFIXES_RECOMPUTED: false
  EMPIRICAL_ENTRY_RADII_PROMOTED_TO_RIGOROUS_ENCLOSURES: false
  NEW_PROOFS: PAPER_PENDING_INDEPENDENT_REVIEW
  HISTORICAL_NOVELTY: not_claimed
EXECUTION:
  HASH_AND_DOCUMENT_VALIDATION_ONLY: true
  NUMERICAL_RUN: false
  SYMBOLIC_SOFTWARE_EXPERIMENT: false
  LEAN_EDIT: false
  LEAN_KERNEL_RERUN: false
  ARISTOTLE_SUBMISSION: false
  QUEUE_OR_SHARED_STATE_EDIT: false
PUBLICATION:
  AUTHORIZED_WRITE_SCOPE: VERDICT_DOC_ONLY
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SIGNED_HEAD_INVARIANT_2026-09-07.md
  METHOD: GitHub_create_file
  COMMIT_AND_READBACK_BLOB: delivery_receipt
  RECEIPT_EFFECT: publication_only
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## 0. Decision and evidence boundary

**The whole three-lobe class has a positive floor:** in the request's conventions,
\[
 \boxed{\mathcal Q(h_0+U_a h_1+U_b h_2)
       \ge \frac3{20}\sum_{i=0}^2\|h_i\|_2^2.}                 \tag{1}
\]
This holds for arbitrary complex smooth profiles supported in the full interval \(I\), with only the two total pole moments zero. It does not use the seven-dimensional computation. Its mechanism is a regional logarithmic-energy gap plus a signed mean/complement estimate. All proofs newly supplied here have scope **ABSTRACT**, verifier **PAPER**, pending independent review.

**The addendum's all-\(n\) success criterion is not met.** No symbolic transition, compensation theorem, or source factorization settling every full signed head is proved here. The search does produce a useful universal identity on an explicitly narrower object: the prime form on the isolated prime-star mean kernel has at most one negative direction, independently of the number of centers. That direction first becomes genuinely negative at four lobes. It is not an inertia theorem for the full heads.

The transition candidate is audited first, as requested. Its exact increment contains a negative shift cost and a difference of two positive coupling corrections. A valid positive innovation identity exists when an additional block is already coercive; this supplies no sign for that block automatically. I therefore select **signed compensation**, not an index-theorem assertion, as the next representation.

### Source keys

**[REQ]** is the complete request at the header's commit. Its fetched UTF-8 bytes, including the final LF, have both stated hashes and both size counts. **[ADD]** is the explicitly authorized addendum, pinned as above. No queue scan selected this task.

**[C]** is `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_FULL_CHAIN_TO_WEIL_2026-09-07.md`, at the request commit, blob `bf4a0cea683c524accde2b90d96a8ebd8b6bc815`. Its source form, head definitions, and forecasts control this review. **[CC]** is `docs/routeB_bus/CHAIN_INDEPENDENT_CHECK_2026-09-07.md` at the same pin. **[TL]** is `docs/routeB_bus/THREE_LOBE_PREFLIGHT_REPORT_2026-09-07.md`. **[LM]** is `docs/routeB_bus/litreview/SOS_WEIL_POSITIVITY_LITERATURE_MAP_2026-09-07.md`. These documents were read; their reported experiments were not rerun.

The analytic review does **not** adopt `100 times the difference of two builds` as a proved entry radius. Agreement between methods is valuable evidence, but an a priori enclosure of the quadrature remainder is still needed to certify the printed 19-digit eigenvalue interval. Equation (1) establishes a different, weaker numerical constant by a proof on the entire class. It does not retroactively validate those entry radii. [FINITE_CELL][CONDITIONAL for the reported analytic enclosure]

Primary external sources used for Q2(c) are listed in Section 6. They supply context and precise limitations, not premises for (1). The folklore assertion that an entire program is closed is not accepted in place of a theorem about its actual conditions.

## 1. Q1(a): exact class, common-profile direction, and signed blocks

Set
\[
 a=\log2,\quad b=\log3,\quad
 \delta=(b-a)/8,\quad I=(-\delta,\delta),\quad
 \ell=2\delta,\quad d=13/125,\qquad \ell<d.
\]
Write
\[
 A(t)=\frac{e^{-t/2}}{1-e^{-2t}},\quad
 c_A=\gamma_E+\log(8\pi)+\pi/2,\quad w_p=\frac{\log p}{\sqrt p}.
\]
The Fourier convention is \(\widehat f(\xi)=\int f(x)e^{-i\xi x}dx\); inner products are antilinear in the first argument. The unchanged source form [C, (C1)] is
\[
 \mathcal Q(f)=\mathcal D(f)-c_A\|f\|^2
 -2\sum_{m\ge2}\frac{\Lambda(m)}{\sqrt m}C_f(\log m)
 +2\Re\{M_+(f)\overline{M_-(f)}\},                         \tag{2}
\]
where \(\mathcal D(f)=\int_0^\infty A(t)\|U_tf-f\|^2dt\),
\(C_f(t)=\Re\int\overline{f(x)}f(x+t)dx\), and
\(M_\pm(f)=\int f(x)e^{\pm x/2}dx\).

For \(h=(h_0,h_1,h_2)\in C_c^\infty(I;\mathbb C)^3\), let
\(v=\sum_i U_{x_i}h_i\), \(x=(0,a,b)\). The total constraints are
\[
 \sum_i e^{\pm x_i/2}\int_I h_i(x)e^{\pm x/2}dx=0.          \tag{3}
\]
The supports are disjoint. Hence \(\|v\|^2=H:=\sum_i\|h_i\|^2\). Only the atoms 2 and 3 act: the correlation lobes are centered at \(0,\pm a,\pm b,\pm(b-a)\), with half-width at most \(\ell\). The next prime-power shift \(\log4\) lies outside the outer support; the lobe at \(b-a\) meets no integer logarithm. Its archimedean term must still be retained.

Define
\[
 V=\begin{pmatrix}1&\sqrt2&\sqrt3\\1&1/\sqrt2&1/\sqrt3\end{pmatrix},
 \quad z=(-1,2\sqrt2,-\sqrt3)^t,\quad e=z/\sqrt{12},\quad Ve=0.
\]
The exact orthogonal common-profile decomposition is
\[
 h=e\phi+k,\qquad \phi=e^*h,\qquad e^*k(x)=0\text{ for every }x. \tag{4}
\]
Both summands separately satisfy (3), since \(Ve=0\). The common-profile summand is infinite-dimensional, not one fixed bump. Orthogonality is in the physical direct-sum \(L^2\) metric. In packet coordinates it is the corresponding **Gram orthogonality**, not ordinary coordinate orthogonality.

Here is the signed operator block explicitly. Let \(L_I\) denote the restricted single-lobe archimedean form \(\mathcal D-c_A\|\cdot\|^2\). Put
\[
 M=\begin{pmatrix}0&-w_2&-w_3\\-w_2&0&0\\-w_3&0&0\end{pmatrix},
 \quad (T_s f)(x)=\int_I A(s+y-x)f(y)dy\quad(s>\ell).
\]
Let \(\mathbb T_{ij}=T_{x_j-x_i}\) for \(j>i\),
\(\mathbb T_{ji}=\mathbb T_{ij}^*\), \(\mathbb T_{ii}=0\), and
\(\mathbb R=M\otimes I-\mathbb T\). On (3), the full form is
\[
 \mathbb Q=I_3\otimes L_I+\mathbb R.                       \tag{5}
\]
Let \(P_e=ee^*\otimes I\). In (4) its exact blocks are
\[
 A_Z=L_I+e^*\mathbb R e,\quad
 E_Z=(I-P_e)\mathbb R e,\quad
 B_Z=(I-P_e)(I_3\otimes L_I+\mathbb R)(I-P_e),              \tag{6}
\]
with \(B_Z\) restricted to the complement satisfying (3). Thus
\[
 \mathcal Q(v)=\langle\phi,A_Z\phi\rangle
 +2\Re\langle k,E_Z\phi\rangle+\langle k,B_Zk\rangle.
\]
The local diagonal part creates no cross term in (4). Both the prime and the nonlocal archimedean cross terms remain in \(E_Z\). The data \(\mathcal D/H\simeq7.137\) concern the frozen profile in [TL], not every \(\phi\).

If \(B_Z-cI\ge\beta I>0\) is independently established, (C23) becomes, for any admissible approximate solve \(Y\),
\[
 A_Z-cI+E_Z^*Y+Y^*E_Z+Y^*(B_Z-cI)Y
 -\beta^{-1}Z^*Z\succeq0,\quad Z=E_Z+(B_Z-cI)Y.            \tag{7}
\]
This is a sufficient **operator** inequality on the common-profile space, not a seven-dimensional certificate. The following proof controls all these couplings without solving that inverse.

## 2. Q1(b): a whole-class proof with a rational ledger

### 2.1 Regional logarithmic energy supplies the missing profile gap

**Lemma 1.** On an interval \(J\) of length \(\ell\), for a complex \(C^1\) function \(f\),
\[
 \int_{x<y\,\in J}\frac{|f(x)-f(y)|^2}{2(y-x)}dxdy
 \ge \|f\|_{L^2(J)}^2-\frac{|\int_J f|^2}{\ell}.          \tag{8}
\]

**Proof.** On \([-1,1]\), define on polynomials
\[
 (Lp)(x)=\int_{-1}^1\frac{p(x)-p(y)}{|x-y|}dy.
\]
This is symmetric. Directly splitting the integral at \(y=x\) gives
\[
 Lx^n=2H_nx^n-\sum_{j=0}^{n-1}
              \frac{1+(-1)^{j+1}}{j+1}x^{n-1-j},
 \qquad H_n=\sum_{j=1}^n1/j,\quad H_0=0.
\]
Consequently \(L\) preserves degree filtrations. By symmetry, the degree-\(n\) orthogonal Legendre polynomial is an eigenvector with eigenvalue \(2H_n\): its image is orthogonal to every lower-degree polynomial and has that leading coefficient. Also
\[
 \frac12\langle f,Lf\rangle
 =\int_{x<y}\frac{|f(x)-f(y)|^2}{2(y-x)}dxdy.
\]
Orthogonal expansion of a polynomial therefore gives (8), because \(H_n\ge1\) for \(n\ge1\). Approximate a \(C^1\) function and its derivative uniformly by polynomials, by first approximating the derivative and then integrating. The error in the displayed energy tends to zero: a Lipschitz error of size \(\varepsilon\) bounds its difference quotient by \(\varepsilon^2|x-y|\). Real and imaginary parts give the complex assertion. Affine rescaling proves (8) on \(J\). QED.

This is an all-profile gap. More generally, the complement of the first \(r+1\) Legendre polynomials has regional gap \(H_{r+1}\), by the same proof and form closure. No table of eigenvalues enters.

For \(0<t\le d<1\),
\[
 A(t)\ge\frac1{2t}.                                      \tag{9}
\]
Indeed \(\tanh t\le t\) implies \(1-e^{-2t}\le2t/(1+t)\), while
\(e^{-t/2}\ge1-t/2\) and \((1-t/2)(1+t)\ge1\).
Zero extension of \(f\) from \(I\) splits \(\mathcal D(f)\) into its regional energy and an exterior potential. The latter is
\[
 \int_I|f(x)|^2\left[\int_{\delta+x}^\infty A(t)dt+
                         \int_{\delta-x}^\infty A(t)dt\right]dx
 \ge2\int_{\ell/2}^\infty A(t)dt\,\|f\|^2.
\]
The inequality follows from convexity of \(s\mapsto\int_s^\infty A\). Combining it with (8)--(9),
\[
 \mathcal D(f)-c_A\|f\|^2
 \ge\beta\|f\|^2+\|f-\ell^{-1}\textstyle\int_I f\|^2,
 \quad \beta=2\int_{\ell/2}^\infty A-c_A>\frac12.           \tag{10}
\]

### 2.2 The exterior constant is bounded without numerical quadrature

For \(s>0\), elementary integration gives
\[
 2\int_s^\infty A(t)dt
 =\log\coth(s/4)+2\arctan(e^{-s/2}).
\]
Using \(\coth x\ge1/x\) and \(2\arctan(e^{-x})\ge\pi/2-x\),
\[
 \beta\ge\log\frac1{\pi d}-\gamma_E-\frac d4
 >\frac{111}{100}-\frac{29}{50}-\frac{13}{500}
 =\frac{63}{125}>\frac12.                                \tag{11}
\]
Here is a finite rational justification of the two nontrivial bounds. The standard bound \(\pi<22/7\) gives \(1/(\pi d)>875/286\). Moreover
\[
 e^{111/100}<\frac{68}{25}\frac{100}{89}
 =\frac{272}{89}<\frac{875}{286}.
\]
For the first inequality use \(e<68/25\), obtained from its Taylor sum through degree five and a geometric tail, and \(e^{11/100}\le100/89\).

For the Euler constant,
\[
 \gamma_E<H_{16}-\log16-\frac1{34}<\frac{29}{50}.
\]
The second inequality follows from \(H_{16}<3381/1000\) and
\(\log2>2(1/3+1/81+1/1215)>693/1000\). The first follows by summing
\(\log(1+1/k)-1/(k+1)\ge1/[2(k+1)^2]\) for \(k\ge16\) and comparing the sum with its integral. Finally \(\ell<d\) follows from \(e^{52/125}>3/2\), already from the quadratic Taylor lower bound. Thus (11) is not an empirical decimal ledger.

### 2.3 Constant cross kernels retain the sign of the free mean

Set
\[
 m_i=\int_I h_i,\quad y_i=m_i/\sqrt\ell,\quad
 g_i=h_i-m_i/\ell,\quad
 H=\|y\|^2+\sum_i\|g_i\|^2.
\]
The \(g_i\) are used in \(L^2(I)\); no assertion that the constant subtraction preserves compact smooth support is required. The energy estimate (10) was applied to the original smooth \(h_i\).

Let \(K\) have zero diagonal and \(K_{ij}=A(|x_i-x_j|)\) off diagonal, and put
\[
 B=M-\ell K.
\]
The prime term splits exactly into \(y^*My+\langle g,(M\otimes I)g\rangle\). Replacing an archimedean cross kernel \(A(s+y-x)\) by \(A(s)\) gives the exact mean contribution \(-\ell y^*Ky\), with an error of norm at most
\[
 \eta=\ell^2\max_i\sum_{j\ne i}
                   \sup_{t\ge|x_i-x_j|-\ell}(-A'(t))<\frac18.
                                                               \tag{12}
\]
To prove this error estimate, use \(|y-x|\le\ell\), the mean-value theorem, and the bound \(\|T\|\le\ell\sup|\text{kernel}(T)|\) on \(L^2(I)\); then use the block row-sum bound for the self-adjoint three-block matrix.

Here is a rational ledger for (12) and for the matrices:
\[
\begin{array}{c|c}
\text{quantity}&\text{proved upper bound}\\\hline
 -A'(a-\ell)&11/4\\
 -A'(b-\ell)&3/2\\
 -A'(b-a-\ell)&8\\
 \eta&d^2(43/4)=7267/62500<1/8\\
 A(a),\ A(b),\ A(b-a)&21/20,\ 5/6,\ 25/16\\
 \|\ell K\|&d(21/20+25/16)=2717/10000<3/10\\
 \|M\|&5/6\\
 \|Me\|&1/4\\
 \|B\|,\ \|Be\|&17/15,\ 11/20.
\end{array}                                                   \tag{13}
\]
All inequalities can be checked by rational operations and Taylor bounds as follows. Since
\[
 A(t)=\frac{e^{t/2}}{2\sinh t}\le\frac{e^{t/2}}{2t},\qquad
 -A'(t)\le e^{t/2}\left(\frac1{2t^2}+\frac1{4t}\right),
\]
and \(-A'\) decreases, evaluate the derivative bound at
\(211/375,112/125,37/125\), respectively, using
\(a>2/3,b>1,b-a>2/5\). The exponential factors there are smaller than \(4/3,8/5,6/5\). The bound
\(e^x\le1+x+x^2/[2(1-x/3)]\) for \(0\le x<3\) proves these; the last also follows from \(e^x\le(1-x)^{-1}\). The bounds for \(A\) use \(e^{1/3}<7/5,e^{1/2}<5/3,e^{1/5}<5/4\).

For the prime bounds, \(w_2<1/2,w_3<16/25\) follow from \(\log2<7/10,\log3<11/10\) and \(\sqrt2>7/5,\sqrt3>55/32\). The logarithm upper bounds follow from finite positive Taylor sums for the exponential. Since \(\log(4/3)<3/10\),
\[
 \|Me\|^2
 =\frac{\log^2(4/3)+w_2^2+w_3^2}{12}
 <\frac{(3/10)^2+(1/2)^2+(16/25)^2}{12}<\frac1{16}.
\]
The star matrix has \(\|M\|=\sqrt{w_2^2+w_3^2}<5/6\). The last row of (13) follows by the triangle inequality.

Crucially, the retained mean has the favorable sign
\[
 e^*Be=\frac{\log(4/3)}6+
 \frac\ell6\left[2\sqrt2 A(a)-\sqrt3 A(b)
                              +2\sqrt6 A(b-a)\right]>0.   \tag{14}
\]
The bracket is positive because \(A\) decreases and \(b-a<b\). This is a source identity valid for the class, not the frozen profile's energy value.

### 2.4 Total moments control only the transverse mean

The zero test is immediate; assume \(H>0\) for the strict final comparison. Decompose \(y=s e+u\) with \(u\perp e\). The matrix
\[
 VV^*=\begin{pmatrix}6&3\\3&11/6\end{pmatrix}
 \quad\text{satisfies}\quad VV^*\succ\frac14 I:
\]
the shifted matrix has first diagonal \(23/4\) and determinant \(5/48\).
Subtracting the constant term from each exponential in (3) therefore gives
\[
 \|u\|\le2\|Vy\|
 \le2\sqrt{47/6}(e^{\ell/4}-1)\sqrt H
 <6\frac{13}{487}\sqrt H<\frac16\sqrt H.                  \tag{15}
\]
The middle inequality follows by Cauchy--Schwarz in the three profiles and then in the two rows. In particular it does not set the free mean \(s\) to zero.

Combining (10)--(15) yields the exact sufficient estimate
\[
\begin{aligned}
 \mathcal Q(v)
 &\ge(\beta-\eta)H+
       \langle g,((I_3+M)\otimes I)g\rangle+y^*By\\
 &\ge\left(\frac12-\frac18-\frac{11}{60}-\frac{17}{540}\right)H
 =\frac{173}{1080}H>\frac3{20}H.                          \tag{16}
\end{aligned}
\]
Indeed \(I_3+M\succeq I_3/6\), \(|s|\le\sqrt H\), and
\[
 y^*By\ge-2\|Be\||s|\|u\|-\|B\|\|u\|^2
 \ge-(11/60+17/540)H.
\]
The favorable term \(|s|^2e^*Be\) was retained until its sign was proved, and only then dropped. This completes (1) on the full requested complex class. QED.

**What replaced the failed rope:** not a smaller estimate for the free mean. The new ingredient is the profile-complement gap (8), followed by the signed source value (14) and transverse-mean estimate (15). The negative coarse budget (C6) and the positive lower envelope (16) concern different sufficient estimates of the same form; there is no contradiction.

## 3. Q1(c): the first exact sign change, and an all-size rank identity

A growing absolute prime sum is not an operator eigenvalue on separated lobes. For centers \(0,\log p_1,\ldots,\log p_r\), suppose the support width is small enough that the only prime-power overlaps are the star edges from 0 to \(\log p_j\). The prime matrix is then
\[
 M_\star=\begin{pmatrix}0&-w^*\\-w&0\end{pmatrix},\qquad
 \|M_\star\|=\left(\sum_{j=1}^r\frac{\log^2p_j}{p_j}\right)^{1/2},
                                                               \tag{17}
\]
not \(2\sum_j\log p_j/\sqrt{p_j}\). Failure of a budget using that larger sum is neither an attained negative value nor a critical lobe count.

There is a useful exact invariant for the common-profile mean sector. Write its coefficients as
\[
 z_0=-\sum_j t_j,\qquad z_j=\sqrt{p_j}\,t_j,
 \qquad \sum_j(p_j-1)t_j=0.                               \tag{18}
\]
These are exactly its two moment equations. If \(L_0(t)=\sum_jt_j\) and
\(L_{\log}(t)=\sum_j(\log p_j)t_j\), then
\[
 z^*M_\star z
 =2\Re\{\overline{L_0(t)}L_{\log}(t)\}
 =\frac12|L_0+L_{\log}|^2-\frac12|L_0-L_{\log}|^2.         \tag{19}
\]
Thus the restricted prime form has rank at most two and at most one negative direction, for every finite isolated star. This is a symbolic statement independent of the number of primes. It is not positivity, and it is not a statement about all directions of \(S_n\).

The physical coefficient metric in (18) is
\[
 \|z\|^2=\left|\sum_jt_j\right|^2+\sum_jp_j|t_j|^2.        \tag{20}
\]
Consequently the one adverse functional can be estimated in this metric after imposing \(\sum(p_j-1)t_j=0\). Euclidean norms of the unweighted \(t\)-coordinates are not interchangeable with it. A prospective compensation proof must pay this functional and its archimedean/profile couplings, rather than the gross prime sum.

### The first failure of positivity on the entire free mean kernel

At three lobes the kernel is the line in (14), with positive prime contribution. At four lobes, centers \(0,\log2,\log3,\log5\), take
\[
 \boxed{z^{(4)}=(-1,4\sqrt2,-4\sqrt3,\sqrt5).}              \tag{21}
\]
Both rows vanish exactly:
\[
 -1+8-12+5=0,\qquad -1+4-4+1=0,
 \qquad\|z^{(4)}\|^2=86.                                 \tag{22}
\]
For any nonzero \(\eta\in C_c^\infty(I)\), the common-profile test
\(f=\sum_jz_j^{(4)}U_{x_j}\eta\) is total-pole-null. The support check uses
\[
 \ell<\min\{\log(6/5),\log(5/4)\}.                    \tag{23}
\]
Thus only the star atoms 2, 3, 5 contribute; the shift 4 and the other center differences do not overlap a correlation lobe. Its prime contribution is exactly
\[
 \frac{\mathcal Q_{\rm prime}(f)}{\|f\|^2}
 =\frac{4\log2-4\log3+\log5}{43}
 =\boxed{-\frac{\log(81/80)}{43}<0.}                      \tag{24}
\]
This strict negative upper value refutes **only** the assertion that every newly free mean direction is prime-positive. It does not refute the full four-lobe form. The positive three-lobe vector extended by zero and (21) also show that (19) has signature \((1,1)\) at four lobes. Larger isolated stars retain those two directions; their remaining mean radical has dimension \(r-3\).

The first honest broken rope of that proposed sign propagation is therefore at **four lobes, largest prime 5**, not at a claimed threshold where \(4\sqrt p\) is attained. Whether a full compensated class estimate survives is a different question.

### Fixed-width stars eventually cease to be stars

At the request's fixed full profile width \(\ell=\log(3/2)/4\), adding the center \(\log11\) introduces, for example,
\[
 \log(11/5)-\log2=\log(11/10)<\ell,\qquad
 \log4-\log(11/3)=\log(12/11)<\ell.                        \tag{25}
\]
The pair of centers 2 and 11 similarly meets the atom 5. These are offset profile correlations, not values determined solely by the means. They cannot be discarded because the center ratios are not exactly integers. Up to largest prime 7 these additional overlaps are absent at this width; at 11 they are present. Eventually the supports themselves also cease to be disjoint unless the width is reduced.

For a general disjoint set of centers, the exact replacement is always
\[
 C_v(t)=\Re\sum_{i,j}\int_I
       \overline{h_i(x)}h_j(x+t+x_i-x_j)dx,                \tag{26}
\]
with zero extensions. Equations (2) and (26) define the true new interactions. Shrinking the width separately for each finite star preserves (19) but does not cover arbitrary tests on an exhausting full interval.

**Remaining rope:** control the negative mean functional in (19), all offset correlations in (26), and their profile couplings by the retained positive regional and exterior energies, with a source rule valid on the full exhausting spaces. No such all-support estimate is proved here. A finite count at which the complete narrow-lobe method fails has not been established.

## 4. Q2(a): exact transition audit

### 4.1 The canonical heads and the core issue

Keep [C, (C12)--(C16)] literally. On \(H_n=L^2(-n,n)\), \(V_n\) spans the uniform-cell indicators and the two restricted exponentials, \(T_n=V_n^\perp\), and
\[
 \mathcal Q=\begin{pmatrix}A_n&E_n^*\\E_n&B_n\end{pmatrix},
 \quad B_n\ge I,\qquad
 S_n(\epsilon)=A_n+\epsilon G_n-E_n^*(B_n+\epsilon I)^{-1}E_n.
                                                               \tag{27}
\]
Here \(\(G_n\) is the physical head Gram. \(A_n\) includes all pole terms. The cutoffs in [C] are an existence construction, not the proposed next computation.

The core step flagged by [CC] can be made explicit. Let \(\mathscr W\) have norm
\(\int\log(2+|\xi|)|\widehat f(\xi)|^2d\xi\). For a supported \(f\in\mathscr W\), the dilation
\(f_r(x)=r^{-1/2}f(x/r)\), \(1/2<r<1\), has strictly interior support. Dilation is uniformly bounded in this norm since
\(\log(2+|\xi|/r)\le C\log(2+|\xi|)\); it is strongly continuous at 1 by approximation by compactly supported continuous Fourier functions. Convolve \(f_r\) with a smooth approximate identity of support radius less than \(n(1-r)\). Its Fourier multiplier is uniformly bounded and tends pointwise to 1, so dominated convergence gives convergence in \(\mathscr W\). The result is in \(C_c^\infty(-n,n)\).

The archimedean form norm is equivalent to this weighted norm after adding a constant multiple of \(\|f\|^2\). The lower logarithmic bound is [C, (C11)]; for the upper bound, split its digamma difference series at \(j+1/4=|\xi|/2\), bound the lower part by a harmonic sum and the upper part by \((\xi/2)^2\sum(j+1/4)^{-3}\). Prime translations and pole functionals are bounded on each fixed support. This proves the required form-core assertion. The head generators lie in the operator domain: their Fourier transforms are \(O(1/|\xi|)\), so multiplication by the logarithmic symbol still gives an \(L^2\) transform. Thus the head-to-tail cross maps in (27) are bounded \(L^2\) functionals. [ABSTRACT][PAPER]

This repairs the sketched domain passage, not the sign. The equivalence recorded in [ADD] follows from this core, completion of the square, and the fixed-test limit with error \(1/n\). It is not used as a positivity premise.

### 4.2 There is a mandatory negative shift cost

The meshes and restricted exponentials defining \(V_n\) do not automatically embed by zero extension into \(V_{n+1}\). One can declare finite enlarged nested heads containing all prior zero extensions and the new canonical head. Their tails are smaller than the canonical tails and retain coercivity. That is a new, explicitly equivalent reduction, not a claim that the original meshes were nested.

For a declared head injection \(J:V_n\to V_{n+1}\) representing zero extension of the same physical functions, let
\(\mathcal K_n=E_n^*(B_n+1/n)^{-1}E_n\). Since the raw full form on an old-support vector is unchanged, the exact pullback increment is
\[
 \boxed{J^*S_{n+1}(1/(n+1))J-S_n(1/n)
 =-\frac{G_n}{n(n+1)}+\mathcal K_n-J^*\mathcal K_{n+1}J.} \tag{28}
\]
Every newly listed prime beyond \(e^{2n}\) has zero autocorrelation on that old-support vector. New spatial cells do not give it a free positive reward. They affect its interaction with new directions and the subsequent minimization.

At a fixed split, for \(0<\epsilon'<\epsilon\), there is an even sharper identity:
\[
 \boxed{S(\epsilon')-S(\epsilon)
 =-(\epsilon-\epsilon')
 \left[G+E^*(B+\epsilon'I)^{-1}(B+\epsilon I)^{-1}E\right]
 \preceq-(\epsilon-\epsilon')G.}                          \tag{29}
\]
The resolvents commute as functions of the same positive \(B\). Thus decreasing the regularizer produces a negative definite increment on every nonzero head, not a positive one.

Equation (28) has a difference of two positive coupling corrections. Its sign is not determined. Refining a head changes what is eliminated; enlarging the ambient domain adds choices in the minimization. These operations cannot be conflated. Equations (28)--(29) obstruct the naive monotonicity argument but do **not** prove that every possible invariant, every embedding, or the literal canonical increment must fail.

New prime terms themselves have both signs. For example, at a newly active prime choose two sufficiently narrow translated copies of the same pole-null profile \((\partial^2-1/4)\eta\), with coefficients \((1,1)\) or \((1,-1)\). Other new prime shifts can be excluded by the finite separation of their logarithms. The selected prime contributes \(-w_p\) or \(+w_p\) after unit normalization. This is an exact sign test on admissible profiles, not a negative value of the complete form.

### 4.3 What a valid positive transition would have to pay

There is a correct innovation identity. Suppose, after eliminating a common coercive tail at the same \(\epsilon\), a refined head is
\(\begin{pmatrix}A&C^*\\C&D\end{pmatrix}\), with \(D\succ0\), and the old head is its Schur complement \(S=A-C^*D^{-1}C\). Then
\[
 \begin{pmatrix}A&C^*\\C&D\end{pmatrix}
 =\begin{pmatrix}S&0\\0&0\end{pmatrix}
 +\binom{C^*D^{-1/2}}{D^{1/2}}
  \begin{pmatrix}D^{-1/2}C&D^{1/2}\end{pmatrix}.             \tag{30}
\]
This is exactly the desired positive-update shape, **provided the innovation block has an independent source proof of positivity**, and the shift change in (29) is also paid. Defining \(D\) to be positive because the new head is positive would be circular.

The two-by-two plant \(A=D=1,C=2\) gives \(S=-3\) and a negative full direction \((1,-1)\). It must fail any gluing argument based on positive diagonal pieces alone. A recurrence written as \(E_n^*S_nE_n\) also requires \(E_n\) to map new coordinates to old coordinates; an embedding in the opposite direction needs the corresponding adjoint or block convention.

**First missing transition inequality:** a source-defined innovation block and its coupling must pay both the new-direction Schur cost and \(G_n/[n(n+1)]\), for every \(n\), with an independently proved base case. No such rule is supplied by the existing cells or by (30). The three-lobe class is a proper support subspace, so its floor is not a base-case proof for the full canonical head \(S_1(1)\).

## 5. Q2(b): compensation and source squares

A positive representation of the entire source, not merely of a reservoir, is required. There are two precise versions worth keeping separate.

For a fixed finite prime set and smooth compact tests, write \(P,Q\) for the two cutoff projections, \(S\) for their common-kernel projection, and
\(D=S-I+P+Q\). Direct multiplication gives
\[
 D+D^2=PQ+QP.                                             \tag{31}
\]
Since \(SP=SQ=0\), this identity holds without a spectral sign assumption. With the source-tested trace identity and all active primes present,
\[
 \mathcal Q(f)=\|T_fS\|_{HS}^2+\|T_fD\|_{HS}^2
 -\operatorname{Tr}(T_f^*T_f(PQ+QP))
 +2|M_c(f)|^2-2|M_s(f)|^2,                                \tag{32}
\]
where \(M_c=\int f\cosh(x/2)\), \(M_s=\int f\sinh(x/2)\).
The trace assertion has the smooth-test domain of the parent Sonin identities; it is not a bare trace of the lacunary angle operator. [ABSTRACT][PAPER, with the identified source-trace theorem]

The first two terms and the positive pole term are genuine source squares. The mixed trace and negative pole term still require compensation. Algebra (31) does not supply their sign. The reported negative plus-channel margin in [REQ] is precisely a warning against making \(\mathcal Q\ge\|T_fS\|^2\) mandatory on all tests; it is not evidence of \(\mathcal Q<0\). Its reported enclosure is not independently re-certified here.

To obtain a **literal head factorization**, use the exact harmonic lift
\[
 \mathcal L_{n,\epsilon}z
 =v_z-(B_n+\epsilon I)^{-1}E_nz,
 \quad z^*S_n(\epsilon)z
 =\mathcal Q(\mathcal L_{n,\epsilon}z)
                      +\epsilon\|\mathcal L_{n,\epsilon}z\|^2. \tag{33}
\]
It is not enough to evaluate the source squares on \(v_z\). Also, separate terms of (32) need a proved extension to the lift's form domain before they can be used as finite matrices. Continuity of their **sum** does not establish continuity of each trace separately.

A domain-safe compensation decomposition is already available directly from (2) on the lift:
\[
\begin{split}
 B_n^+[z]&=\mathcal D(f)+2|M_c(f)|^2+\epsilon\|f\|^2,\\
 A_n^-[z]&=-c_A\|f\|^2-2\sum_m w_mC_f(\log m)-2|M_s(f)|^2,
 \qquad f=\mathcal L_{n,\epsilon}z.
\end{split}                                                \tag{34}
\]
Then \(S_n=A_n^-+B_n^+\) and \(B_n^+\succeq0\) by construction. An all-\(n\) proof of the separate, physical-Gram inequalities
\[
 A_n^-\succeq-\delta_nG_n,\qquad
 B_n^+\succeq\delta_nG_n                                  \tag{35}
\]
would meet the addendum. But choosing \(\delta_n\) from an unknown minimum, or inserting the desired comparison as a field, would not. A relative domination of the negative part by the positive energy may be weaker than these scalar bounds and is admissible if actually proved.

The new mechanism in Section 2 is a concrete success of this kind: exterior energy pays a fixed baseline; regional energy controls the mean-zero profiles; total moments make the transverse mean small; the surviving mean has a proved signed value. Equation (19) shows the next structural change: the mean now contains one adverse functional. Equation (25) shows the following change: offset correlations enter. A uniform estimate paying those terms on a full support, rather than just an isolated star, is the **minimal missing compensation inequality**. This review does not supply it.

For a Gram/SOS proposal \(S_n=X_n^*X_n+R_n\), \(R_n\succeq0\), the same issue remains: \(X_n\) and \(R_n\) must be defined from source data and their identity proved. \(X_n=S_n^{1/2}\) is unavailable before positivity. Congruence or a change of basis does not remove a negative direction. Neither failure of (35) for one decomposition nor failure of a stronger reservoir minorant refutes every possible source factorization.

## 6. Q2(c)--(e): index shape, zero mirror, and the next deciding object

### 6.1 What a finite index theorem would actually say

A sufficient finite **Hodge-index package** would give source-defined Hermitian spaces \((W_n,J_n)\), vectors \(a_n\) with \(J_n(a_n,a_n)>0\), and linear maps \(\Phi_n\) such that
\[
 \operatorname{ind}_+(J_n)=1,\qquad
 J_n(a_n,\Phi_nz)=0,\qquad
 S_n(1/n)=-\Phi_n^*J_n\Phi_n+U_n^*U_n.                    \tag{36}
\]
A form of positive index one is nonpositive on the orthogonal complement of a positive vector: otherwise that vector and a positive orthogonal vector span a positive two-plane. Thus (36) would prove PSD. The construction and identity would have to work symbolically for all \(n\), retain the exact pole and Schur terms, and include the source/coordinate crosswalk.

The orthogonality condition is essential. With \(J=\operatorname{diag}(1,-1)\) and \(\Phi(1)=(1,0)\), the index statement holds but \(-\Phi^*J\Phi=-1\). Saying that \(S_n\) itself has negative index one is not a positivity theorem. Nor does subtracting an indefinite rank-two pole block from an arbitrary Gram matrix establish the required orthogonality or inertia.

**Literature boundary.** Bombieri's Clay description, printed pp.9--10, relates the geometric-case sign to the algebraic index theorem and explicitly presents an analogous number-field theorem as speculative. Both pages were checked visually. It is not a no-go theorem. **[BOM]**

Connes--Consani, *The Riemann--Roch strategy: Complex lift of the Scaling Site*, arXiv:1805.10501v1, Introduction and Section 3, constructs parts of a scaling-site framework and describes the Riemann--Roch strategy; the required cohomological/sign ingredients are not supplied as a package realizing (36). Haran, *Non-Additive Prolegomena*, arXiv:0911.3522v1, Section 8.7, explicitly labels the proposed intersection pairing and Frobenius-divisor relations as conjectural. **[SCALE, HAR]**

Deninger's 1998 ICM article develops the cohomological/dynamical analogy. The abstract of *Dynamical systems for arithmetic schemes*, arXiv:1807.06400v1, describes a dynamical construction; that abstract does not provide a positive pairing and an exact map to these heads. I do not promote it to such a theorem. **[DEN98, DEN18; DEN18 read at abstract level]**

The ordinary fiber product \(\operatorname{Spec}\mathbb Z\times_{\operatorname{Spec}\mathbb Z}\operatorname{Spec}\mathbb Z\) is just \(\operatorname{Spec}\mathbb Z\). An intended absolute or arithmetic square requires its own specified category and construction; the notation alone does not give a surface carrying (36).

Two claims in [LM] require narrower wording. Conrey--Li, arXiv:math/9812166v1, refutes the particular positivity conditions discussed there, including the structural objection in Section 4; this does not refute all de Branges representations. And the map does not establish an exhaustive theorem that there are no other SOS mechanisms. Its own CC20 entry concerns a genuine restricted source-positive trace. The compact-window and pointwise-envelope claims recorded for Zhu have their stated certificate-class boundary; no Zhu numerical constant, priority claim, or barrier estimate is used in this proof. **[CL, LM]**

None of these checked sources supplies (36) for our heads. None proves that such a package, or a different compensation identity, is impossible. The rank-two mean identity (19) is a useful finite sign pattern, but it is not an arithmetic intersection theory.

### 6.2 The zero-side mirror must use the harmonic lift

Under RH, **only as a guide**, (33) gives
\[
 z^*S_n(\epsilon)z
 =\sum_\rho|\widehat{\mathcal L_{n,\epsilon}z}(\gamma_\rho)|^2
                  +\epsilon\|\mathcal L_{n,\epsilon}z\|^2. \tag{37}
\]
The functionals are not just zero evaluations on \(V_n\). Tail elimination changes them. The evaluation Gram on \(V_n\) represents the raw block \(A_n\), not its Schur complement. The extension of the zero-side expression to form-domain lifts must likewise be taken through its established form closure, not an unproved pointwise series.

There is no proposed finite-height rank bound for the full head. Under this same conditional guide,
\[
 S_n(\epsilon)\succeq\epsilon G_n\succ0,                   \tag{38}
\]
because \(\mathcal Q\ge0\) and \(\|v_z+y\|^2\ge z^*G_nz\). Thus the shifted head has full rank. A truncated sum of zero evaluations has rank bounded by the number retained, but its omitted tail and the norm term in (37) can complete the rank. A resolution height is not an exact spectral cutoff.

For the raw seven-dimensional packet, a zero-side comparison **is informative as a coordinate diagnostic**. Use the exact [TL] kernel basis and Gram, the source transform convention, both signs of the ordinates, and multiplicities. For a real basis that is not globally even, a pair of zeros gives twice the **real part** of its outer-product matrix, not blindly twice one complex outer product. This distinction matters for arbitrary complex coefficient vectors.

A conditional list of first zeros is insufficient for a rigorous full error. One usable absolute tail budget is as follows. If every basis function is supported in \([-R,R]\), set, for an integer \(m\ge2\),
\[
 C_i(m)=e^{R/2}\sum_{j=0}^m\binom mj2^{-(m-j)}\|f_i^{(j)}\|_1.
\]
Integration by parts bounds its Laplace evaluation at \(\sigma+i\gamma\), \(|\sigma|\le1/2\), by \(C_i(m)|\gamma|^{-m}\). If \(B(X)\) is a proved upper bound for the number of zeros with \(0<\gamma\le X\), then a safe entrywise tail beyond \(T\) is
\[
 2C_i(m)C_j(m)\sum_{k\ge0}
       B(2^{k+1}T)(2^kT)^{-2m}.                           \tag{39}
\]
This absolute estimate allows off-line zeros in the omitted tail. It needs a proved counting bound, coverage of all zeros up to \(T\), derivative-norm enclosures, and conversion to the physical Gram norm. It does not assume that omitted terms are positive. The comparison can expose a normalization or coordinate defect; agreement does not supply any all-\(n\) invariant. No such run is performed here.

### 6.3 Which object to test next

I tested the transition shape first on paper through (28)--(30), and select compensation second. An index construction has much less source data available; an unconstrained SOS search risks encoding the unknown sign in a square root.

The cheapest decisive next check is an **independent proof audit of (8)--(16)**. It replaces the seven-dimensional packet by a three-component local-mean estimate plus a proved infinite profile complement. It does not require the enormous canonical \(K_1\).

The next prospective numerical discriminator, only after that audit, is the first overlap-bearing center set
\(0,\log2,\log3,\log5,\log7,\log11\), not a larger unstructured positive packet. Use a profile head of low Legendre degrees plus the exact exponential moment representers. On its orthogonal complement the regional gap is \(H_{r+1}\) from Lemma 1. More explicitly, let \(C_{\rm int}\) be a proved sum of operator-norm bounds for the off-diagonal archimedean kernels and the prime-shift blocks from (26), and choose \(r\) so that \(\beta+H_{r+1}-C_{\rm int}\ge1\). On the complement of this head the pole term vanishes, so this gives the required tail floor. These bounds are finite: the archimedean block norm is at most \(\ell A(|x_i-x_j|-\ell)\), and each prime-shift block has norm at most its weight. No useful numerical dimension is claimed before this fixed six-center budget is evaluated. Include profiles occupying the full allowed width, so the offsets in (25) cannot be missed by the narrower frozen bump.

Assemble (26) for every active prime power, including 4, 8 and 9 when their correlations are nonzero, and retain every archimedean lag. Test the **candidate compensation residual**, its mean negative direction and its couplings, not only the eigenvalues of the complete packet. A negative upper witness for the proposed residual refutes that mechanism. A positive packet without a complement and an all-size identity is not addendum success.

## 7. Q3: formalization order, route map, and one directive

The inexpensive protective algebra is worth formalizing before the expensive trace machinery, but the newly needed regional gap should not wait behind it. This is an ordering proposal, not authorization to edit Lean in this batch.

| Order | Theorem-sized item | What it protects or supplies |
|---|---|---|
| 1 | Exact moment rows, physical Gram congruence, the vectors (14), (21), and the prime identity (19) | Prevents deleting the free mean and prevents extending its favorable sign incorrectly. |
| 2 | Schur completion, residual sandwich, and shift difference (29) | Preserves the full tail residual and the correct direction of every envelope. |
| 3 | Regional logarithmic-energy gap (8), its Legendre complement, and the rational ledger (11)--(16) | Supplies the actual whole-class positive theorem, not a packet wrapper. |
| 4 | Projection algebra (31) and the existing pole-gauge interfaces | Useful exact algebra; its trace/sign application must remain a separate theorem. |
| 5 | Dilation/mollifier form core and bounded head-to-tail cross maps | Closes the previously sketched domain transport without assuming positivity. |
| 6 | Mellin source trace formula, Hankel trace-class estimates, and the global digamma/Bernstein tail | Larger analytic ports; not needed to prove (1) from the already locked form. |

Expected engineering difficulties are the singular integral's quadratic-form domain, the Legendre spectral identity, supported weighted-Fourier approximation, and trace-ideal composition. These are **forecasted formalization tasks**, not claims that the current Mathlib lacks named APIs. No current Mathlib inventory or kernel build was run. Search existing source declarations and exact types before creating new ones.

### Candidate representations and exact remaining demand

| Representation | Kill-power / cost, ordinal | What still has to be proved |
|---|---|---|
| Signed mean/profile compensation | 9/10 / 4/10 for the local theorem audit; global cost unknown | Pay the rank-two mean defect and offset correlations on full exhausting spaces, uniformly by one source rule. |
| Nested innovation / shorted-form recurrence | 10/10 / 6/10 for a structural preflight | Prove each innovation block and its shift budget independently; formula (30) alone assumes the critical sign. |
| Geometric index realization | 10/10 potential / 10/10 construction cost | Produce the spaces, primitive map, and exact source identity in (36), not only the index analogy. |

**MINIMAL MISSING IDENTITY / INEQUALITY:** a source-defined all-size compensation paying (19), (26), and the Schur coupling cost, or an innovation identity (30) whose positive block and decreasing-shift budget are proved for every full support. In matrix language it must imply (35), a weaker relative domination, or a manifestly positive factorization of the unchanged \(S_n(1/n)\). Its proof must contain no unresolved per-\(n\) test.

**DISCRIMINATOR:** for a proposed identity, evaluate the exact Hermitian defect on the free-mean and offset-correlation directions before testing PSD. For a zero-consistent scalar margin, use two-sided source enclosures of the *same residual*. A strict negative upper endpoint refutes that candidate; a negative lower endpoint does not. Zero itself may be a true kernel and does not justify adding an artificial gap.

### One CODEX DIRECTIVE — independent paper audit, no execution expansion

**Target:** `THREE_LOBE_REGIONAL_LOG_GAP_COMPENSATION_REVIEW`.

**Inputs:** [REQ], [C, (C1)--(C7), (C22)--(C23)], and Sections 1--3 of this verdict.

**Task:** independently check the regional factor of two, the Legendre eigenvalue \(2H_j\), the exterior constant, all rational bounds in (13), the total-moment estimate (15), and the source cross-kernel sign. Establish (1) on the full complex class, or return the first failed inequality and its weakest repair. Use (21)--(24) as the exact guard against an illicit all-center mean-sign extension.

**Forbidden shortcuts:** importing a packet eigenvalue; imposing separate pole-nullness on each profile; shrinking \(I\); discarding the lag \(b-a\); replacing the physical Gram; treating empirical build differences as enclosures; using an assumed all-support positivity statement.

**Success:** independent paper confirmation of \(\mathcal Q(v)\ge3H/20\) with precisely (3), and confirmation that the four-lobe counterexample concerns the prime part only. **Failure:** `INVARIANT_REGIONAL_GAP_FACTOR_ERROR`, `INVARIANT_THREE_LOBE_SIGNED_LEDGER_GAP`, or `INVARIANT_SOURCE_CLASS_CHANGED`, with the exact line and a witness when applicable. A formalization/API problem is research debt, not a mathematical negative.

**Validation boundary:** no new numerical run, no Lean edit, no queue mutation, no Aristotle, and no route promotion in this adjudication. Future formalization requires its own source record and `lake`/axiom gate. This document does not provide one.

## 8. Scoring, dependency epistemics, and closeout

### Frozen observer predictions

| Prediction | p | Fate, without altering the event |
|---|---:|---|
| P_THREE_LOBE_CLASS_THEOREM | 0.50 | CONFIRMED_AT_PAPER_LEVEL: (16) proves an explicit positive constant on the whole requested class. Independent review is pending. |
| P_NARROW_LOBE_BREAK_AT_PRIME_SUM | 0.65 | UNRESOLVED_AS_A_COMPLETE_ROAD_BREAK: the proposed gross-sum diagnosis is rejected, since the sum is not the star norm. The free-mean sign rope fails at four lobes; no count killing every compensated repair is proved. |
| P_INVARIANT_SHAPE_IS_INDEX | 0.30 | REFUTED_AS_SELECTION_FORECAST: compensation is selected after the transition audit. |
| P_MONOTONE_RECURRENCE_OBSTRUCTED | 0.60 | CONFIRMED_WITH_SCOPE: (28)--(29) expose the uncontrolled increment and its negative shift cost; not a refutation of every possible invariant. |
| P_ZERO_MIRROR_INFORMATIVE | 0.55 | CONFIRMED_AS_COORDINATE_DIAGNOSTIC: the raw packet comparison is useful with (39), but no computation is performed and it has no universal-sign force. |
| P_FORMALIZE_ORDER_AS_GUESSED | 0.70 | PARTIAL: the protective algebra agrees; the new regional gap and the core repair receive explicit priority, while the heavy trace formula is deferred. |

### Frozen CHAIN registrations

| Prediction | p | Fate |
|---|---:|---|
| P_CHAIN_THREE_LOBE_MEAN_FALSIFIER_SURVIVES | 0.98 | CONFIRMED_BY_REPORTED_INDEPENDENT_REVIEW [CC, Sections 1--2]: the null vector, copied-mean failure and scope of the negative sufficient budget were accepted. |
| P_CHAIN_EXPLICIT_FULL_SUPPORT_TAIL_SURVIVES | 0.90 | PARTIAL_INDEPENDENT_CONFIRMATION: [CC] accepts the tail and Schur algebra but flags the form core as sketch-level. Section 4.1 supplies a new proof; self-supply is not independent acceptance of the frozen complete event. |
| P_CHAIN_FROZEN_SEVEN_DIMENSIONAL_THREE_LOBE_FLOOR | 0.65 | MATHEMATICAL_FLOOR_CONFIRMED_ON_PAPER_BY_(1): the exact frozen packet is a subclass and has floor at least 3/20, hence at least 1/100. The reported interval certification and 19-digit eigenvalue enclosure remain conditional on validated entry radii. |

The [TL] minimizer alignment and the Euler--Gram numbers remain reported finite diagnostics. Nothing here scores their precision as an independent interval theorem.

### New prospective registrations

These are forecasts for subsequent independent checks, registered after this proof attempt and its supplied data. They are not blind predictions preceding the observer's runs.

```yaml
P_INVARIANT_THREE_LOBE_PAPER_REVIEW:
  probability: 0.85
  event: independent_review_accepts_3_over_20_on_the_unchanged_full_complex_class
  fate: PENDING
P_INVARIANT_PRIME_STAR_RANK_REVIEW:
  probability: 0.99
  event: independent_review_accepts_19_and_the_strict_four_lobe_value_24
  fate: PENDING
P_INVARIANT_OFFSET_MODEL_CHECK:
  probability: 0.95
  event: a_source_valid_full_width_six_center_assembly_contains_the_nonstar_terms_25
  interpretation: implementation_discriminator_of_an_already_derived_identity
  fate: PENDING_NO_RUN_HERE
```

### Consumer-first record

**DOWNSTREAM_CONSUMER:** published Weil criterion on all complex compact smooth tests in convention (2).

**ACTUAL_CONSUMER_REQUIREMENT:** nonnegativity of the same source form on that full class. The all-support shifted-head contract remains equivalent through the repaired core and [C]'s fixed-test limit.

**ORIGINAL_REQUESTED_OBJECT:** one symbolic transition invariant, separate compensation theorem, or source Gram/SOS for all \(n\). **ORIGINAL_OBJECT_IS:** the particular three proposed representations are `NOT_NECESSARY`; some proof of the consumer sign is required, but no theorem makes one representation mandatory.

**KNOWN_WEAKER_INTERFACES:** a relative source-energy domination rather than two scalar eigenvalue bounds; a compatible exhausting subfamily with proved recovery of every fixed test; or source lower errors tending to zero on every fixed compact test. Each must retain the exact form, moment conditions, topology and all-support quantifier. Shrinking isolated-star classes alone do not supply that recovery.

**FAILURE_TYPE / EPISTEMIC_STATUS:** `COUNTEREXAMPLE / MATHEMATICALLY_DEAD` only for the two exact theorem shapes in the header, with evidence (24) and (29). `NO_DERIVATION / RESEARCH_DEBT` for all-size compensation and innovation positivity. `NO_SOURCE / RESEARCH_DEBT` for a geometric realization (36) in the checked sources. No `ROUTE_FAMILY` death is asserted.

**NOVELTY_AXIS:** replacing absolute mean estimates by regional profile coercivity and an explicitly signed finite mean block; tracking the one adverse functional until true offset correlations enter. Historical priority is not claimed.

**REOPEN TRIGGERS:** a source-uniform bound for the negative functional and offset/coupling terms reopens compensation; an independently positive innovation construction paying (29) reopens recurrence; an actual source pairing and primitive map reopens the index realization. For the empirical entry radii, provide a proved quadrature and arithmetic enclosure, not another convergence plot.

### What changed, and what must not recur

The three-lobe infinite-profile sign is now proved on paper. The first free-mean extension has a precise negative prime witness and a rank-two identity. The moving-head recurrence has a signed, typed increment instead of a monotonicity slogan. The form-core sketch has been expanded. The all-support sign mechanism is still unproved.

Do not repeat: counting a positive packet as an all-size induction; deleting the free mean; identifying a failed absolute budget with a negative source value; copying a prime-star matrix after offset overlaps appear; evaluating the raw zero Gram and calling it a Schur head; or using a geometric program's name as its missing positivity theorem.

```yaml
META_CLOSEOUT:
  PROGRESS_CLASS: PROOF_PROGRESS
  COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
  ROUTE_SCORE: 5
  SCORE_SCOPE: local_class_and_mechanism_precision_not_global_completion
  WHAT_BECAME_SMALLER:
    - CHAIN_C22_now_has_a_whole_class_paper_proof
    - isolated_star_mean_defect_is_one_adverse_functional
    - first_mean_sign_change_and_first_fixed_width_nonstar_overlap_are_explicit
    - recurrence_must_pay_a_known_negative_shift_and_a_signed_coupling_difference
  GLOBAL_HARD_SUCCESS: false
  CURRENT_SMALLEST_GLOBAL_GAP: source_uniform_compensation_or_innovation_sign
  NEXT_DECISIVE_TEST: independent_regional_log_gap_and_signed_ledger_review
  MEMORY:
    target: REQ-2026-09-07-INVARIANT
    status: PROGRESS
    invariant_learned: preserve_the_signed_mean_and_the_full_profile_complement
    forbidden_future_move: replace_an_all_support_mechanism_by_another_positive_packet
    next_decisive_test: verify_8_through_16_then_test_the_offset_terms_25
PUBLICATION_HANDOFF:
  BRANCH: rh_clean
  PATHS_WRITTEN:
    - docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SIGNED_HEAD_INVARIANT_2026-09-07.md
  LEAN_FILES_WRITTEN: []
  LEAN_GATE_COMMANDS: NOT_APPLICABLE_DOCUMENT_ONLY
  EXPECTED_AXIOM_PROFILE: NOT_APPLICABLE_NO_KERNEL_GATE
  COMMIT_AND_READBACK_BLOB: delivery_receipt
  GATE_RESULT_CHANGES: publication_status_only
```

### External bibliography and exact reading scope

[BOM] E. Bombieri, *Problems of the Millennium: the Riemann Hypothesis*, Clay Mathematics Institute problem description, printed pp.9--10; primary PDF text and page images checked.

[SCALE] A. Connes and C. Consani, *The Riemann--Roch strategy: Complex lift of the Scaling Site*, arXiv:1805.10501v1, Introduction and Section 3; primary full text checked.

[HAR] S. Haran, *Non-Additive Prolegomena*, arXiv:0911.3522v1, Section 8.7, especially the proposed intersection pairing and Frobenius relations; primary full text checked.

[DEN98] C. Deninger, *Some analogies between number theory and dynamical systems on foliated spaces*, ICM 1998, Vol. I, pp.163--186; primary publisher description consulted, not imported as a proved positivity theorem.

[DEN18] C. Deninger, *Dynamical systems for arithmetic schemes*, arXiv:1807.06400v1; abstract-level reading only.

[CL] J. B. Conrey and Xian-Jin Li, *A note on some positivity conditions related to zeta and L-functions*, arXiv:math/9812166v1, Sections 3--4; primary full text checked.

The analytic starting point (2), the previously established smooth Sonin identity, and the canonical head definitions are the pinned project sources [C] and its declared parent lineage. The new regional and signed-mean proofs above are given directly; no external conjectural index, zero-location assumption, or packet spectrum is used in them.

## 9. PROSHKA'S OWN LINE

I choose compensation because the three-lobe calculation exposes an energy that can actually be bounded on every profile.
The regional logarithmic gap is the useful new input, not the size of the packet eigenvalue.
It lets the free mean remain present instead of pretending that two moments remove three means.
The transition approach was checked first, and its shrinking regularizer has a real negative cost.
A positive-update identity is still possible, but only after the new innovation block has earned its sign.
The index approach is attractive because one geometric identity could control every scale.
It is not my first choice because the required source pairing and primitive map are not currently supplied.
The first move beyond this batch is independent verification of the regional-energy proof and its rational ledger.
A wrong factor of two, an omitted archimedean lag, or an illicit separate moment constraint would kill that proof.
The second move is to retain the single adverse mean functional when more centers are added.
That move must also retain the offset prime correlations that appear at the center eleven.
An exact source residual with a negative upper witness would kill the proposed compensation, not necessarily the full form.
Another positive finite packet without an invariant would fail the stated goal even if its numerics were impeccable.
I would ask for the exact full-width profile interaction operator at the first nonstar overlaps.
I would not ask for more ordinates or a larger copy of the same seven-dimensional packet first.
For a recurrence I would ask for a precise embedding and a definition of the newly eliminated space.
Without those, comparing two matrices can hide a change of variational problem.
The four-lobe vector surprised me because the prime sign changes before a large-prime estimate is relevant.
The same computation also gives a useful restriction: the isolated mean defect has only one adverse direction.
That is a genuine symbolic pattern, but its domain is smaller than the full support head.
I distrust calling empirical refinement differences rigorous radii without a remainder theorem.
I also distrust the phrase that an entire mathematical program is closed when only particular positivity conditions were refuted.
The three-lobe proof is a result worth preserving even though it does not finish the all-support mechanism.
The addendum correctly prevents that local success from being relabeled global success.
No amount of confidence in the numerical trend supplies the missing mixed-energy inequality.
The next useful invariant must account for that inequality without asking for a fresh sign check at each scale.
The present verdict states exactly where that requirement remains unmet.
It also leaves a concrete paper theorem and a sharper falsifier, rather than another renamed unknown alone.
