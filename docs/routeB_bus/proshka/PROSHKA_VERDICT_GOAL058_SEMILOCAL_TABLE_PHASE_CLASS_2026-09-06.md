# STATUS: TRY_PHASE_CLASS_WITH_COMPACT_NON_HILBERT_SCHMIDT_ANGLES_AND_SMOOTH_TRACE
```yaml
PRIMARY: TRY_PHASE_CLASS_WITH_COMPACT_NON_HILBERT_SCHMIDT_ANGLES_AND_SMOOTH_TRACE
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-06-SEMITABLE
BOUNDARY_ID: GOAL058_SEMILOCAL_TABLE_PHASE_CLASS_AND_TRACE_DOMAIN
RESULT:
  Q1: PARTIAL_WITH_PRECISE_REMAINDER
  Q2: PROVED_ON_CLASS
  Q3: PARTIAL_WITH_PRECISE_REMAINDER
REQUEST_LOCK:
  COMMIT: 1cf04954049cc0e9817d4d5e9723ae7a66ac7b69
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_SEMILOCAL_TABLE_PHASE_CLASS_2026-09-06.txt
  GIT_BLOB: 4cb0d9b8ecb28d124f90946a47986eaf8f29ce86
  SHA256: 4733b97580cbcd93e72c80828dbe5cc5c50a2a3ad32598de6a33d562b9fbd5cd
  BYTES: 12101
  LINES: 109
  FINAL_LF: true
  FETCHED_UTF8_REENCODING_HASHES_RECOMPUTED: true
EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SEMILOCAL_TABLE_PHASE_CLASS_2026-09-06.md
PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_SECOND_EXPRESSION
  SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
  TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false
DECISIONS:
  R1_RETAINED_ON_EXPLICIT_POLE_NULL_PHASE_CLASS: true
  R1_CLASS_SIGN_PROVED: false
  RAW_ANTISYMMETRIC_BUMPS_AUTOMATICALLY_POLE_NULL: false
  PHASE_TESTS_HAVE_IDENTICAL_ARCHIMEDEAN_ENERGY: false
  I_MINUS_U_RANGE_EQUALS_WEIGHTED_B_IMAGE_CLASS: false
  ANGLE_OPERATOR_COMPACT: true
  ANGLE_OPERATOR_HILBERT_SCHMIDT: false
  ANGLE_OPERATOR_TRACE_CLASS: false
  D_S_TRACE_CLASS_WITHOUT_TEST: false
  SMOOTH_TEST_TIMES_D_S_TRACE_CLASS: true
  SMOOTH_TEST_TIMES_SONIN_TRACE_CLASS: true
  SMOOTH_TEST_TIMES_I_MINUS_P_MINUS_Q_TRACE_CLASS: true
  NEW_TRACE_REGULARISATION_REQUIRED_ON_SMOOTH_TESTS: false
  POINTWISE_ANGLE_DISTRIBUTION_SERIES_CONVERGENCE: not_claimed
  EXACT_SINGULAR_VALUE_ASYMPTOTIC: not_proved
SCORING_REPAIRS:
  RAW_BUMPS_DO_NOT_REFUTE_FROZEN_POLE_NULL_FORECAST: true
  NARROW_ETA_FORECAST_NOT_SCORED_ON_GAUSSIAN_SUBSTITUTES: true
  POLE_NULL_TRIPLE_REMAINS_UNRESOLVED: true
CLOSES: [REQ-2026-09-06-SEMITABLE]
CLOSES_ANALYTIC_RH_SUPPLIERS: []
CLOSED_PAPER_OBLIGATIONS:
  - SEMILOCAL_ANGLE_COMPACTNESS_AND_SCHATTEN_THRESHOLD
  - SEMISIGN_N1_SMOOTH_TEST_TRACE_DOMAIN
OPENS: []
EVIDENCE_CUTOFF: request_commit
POST_REQUEST_METADATA_SEEN: 8c3615f02a131c710193e03b3c548ae373ee5b24
POST_REQUEST_REPORT_CONTENT_READ: false
PREDICTIONS_PRECEDE_OTHER_AGENTS_NEW_RUNS: not_claimed
OBSERVER_TABLE_STATUS: FINITE_DIAGNOSTIC_NOT_INTERVAL_CERTIFICATE
NEW_PROOFS_VERIFIER: PAPER
INDEPENDENT_KERNEL_VERIFICATION: false
NOVELTY_IN_LITERATURE: not_claimed
NUMERICAL_RUN_PERFORMED: false
LEAN_EDIT_PERFORMED: false
ARISTOTLE_SUBMISSION: false
REPOSITORY_WRITE_SCOPE: EXPECTED_VERDICT_DOCUMENT_ONLY
QUEUE_OR_SHARED_STATE_EDIT: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## 0. Decision, evidence and conventions

The phase lead is retained, with an exact test class and a full mixed-term budget. It is not a new positivity theorem yet. The angle warning has a stronger rigorous answer than the table alone: for one finite prime the genuine compression is compact, belongs to every Schatten class of exponent greater than two, but is not Hilbert--Schmidt. Nevertheless, after insertion of a smooth compact multiplicative test, each term of the Sonin/angle trace split is an ordinary trace-class operator. Thus the divergence of the bare angle sum does not invalidate the tested identity and does not require an additional renormalized trace.

These are new PAPER derivations in this document, not Lean results or claims of historical priority. The sign table is evidence about the stated finite implementations, not a theorem about their limiting operator. No experiment has been run here. The COMPARISON was read first; its unresolved classifications override B's later unilateral sign assertions.

### Sources used

[C20] Connes--Consani, arXiv:2006.13771v1, 57-page version: Proposition 1.5(iv), Theorem 4.7 (83)--(84), pp.27--28; Theorem 6.11, pp.48--49; Appendix D, Lemma D.1, pp.51--52. The latter supplies the Schwartz/half-line commutator context; a direct trace-class proof is included below.

[C23] Connes--Consani--Moscovici, arXiv:2310.18423v2: Definition 4.5 and Proposition 4.6, pp.21--22; Proposition 4.7, (57)--(59), pp.22--23; Theorem 4.6, p.23. In particular the finite Euler map is a bounded invertible map of Sonin spaces, not an isometry.

[C26] Connes, arXiv:2602.04022v1, (22), printed p.32, and endnote 11, p.36. The fixed-cutoff trace formula is used with its original normalization. Relevant PDF formulas and the v2 Sonin theorem were checked visually.

[P0] SEMILOCAL at commit 3242ada9ee58c0716d64192c9749fcfa742af806, blob 7b4e6562c358902eb1c7204b1fcded7a2ee6b91d. [P1] SEMISIGN at commit 59aabc180e35400a13d28481d7141e62c1985e5a, blob 5e65501a938aa08b63a066096a09a96724f57891. Their mounted source bytes and definitions, not prior conversational summaries, are the parent basis.

At the request pin: [TC] COMPARISON, blob 3fdbb26af50fb846bbe0a95742453b1004a6afb7; [TA] table A, blob 6289d56abfba95698da06b76bb469d5cce9b652b; [TB] table B, blob eb587d905e0d1ce4c0a7b80b987a12df06fd09da; [IC] SEMISIGN independent check, with the request's SHA prefix d25cf67ac3f66c71. The test implementation `phase5_codex/semitab_B/tests.py`, blob 249ae4b54e93774b00ea101109076c495fd9ccc8, was read but not executed.

Write U_c v(x)=v(x-c), T_v h=v*h, a=log 2, r=2^(-1/2), w=a/sqrt(2). Use a_inf(t)=e^(-t/2)/(1-e^(-2t)) to avoid confusing this density with the separation a. The Hilbert space of the pair is the full log-line L2, equivalently the physical half-line under h(u)=u^(-1/2)v(log u). P_lambda is the physical cutoff 0<u<=lambda. The convolution test v and a carrier vector on which the projection acts are not the same object.

For f_v=k_v*k_v^*, k_v(u)=v(log u), let

\[
 n(v)=\|T_v\mathsf S_{2,1}\|_{HS}^2,\quad
 e(v)=E_{2,1}(f_v),\quad
 L_2(v)=\mathcal D(v)-c_A\|v\|^2-2\sum_{j\ge1}a2^{-j/2}C_v(ja).
\]

Here C_v(t)=Re int conj(v(x))v(x+t)dx and c_A=gamma+log(8pi)+pi/2. At lambda=1 the contact term ell=0. Once the trace domain is proved in section 5, e=n-L_2 is an exact identity. On support diameter at most log 3, Q(v)=L_2(v)+P_02(v), with P_02=2 Re(A_+ conjugate(A_-)).

## 1. Score the original forecasts, without changing their tests

The old probabilities remain frozen. A reported numerical confirmation below is a diagnostic outcome, not an interval-certified sign.

| Forecast from P1 | p | Fate in this audit | Exact reason |
|---|---:|---|---|
| P_WIDE_BUMP_E_POSITIVE_FOR_B3_4_6 | 0.99 | CONFIRMED_DIAGNOSTIC_WITH_COVERAGE_SPLIT | b=3 in A and B; b=4,6 only in B. The exact broad-bump theorem is independent of these implementations. |
| P_NARROW_SINGLE_BUMP_E_POSITIVE | 0.65 | EXACT_TEST_UNTESTED; QUALITATIVE_CORROBORATION | P1 registered normalized eta_delta0 at two centers. B's ordinary bumps are cut-off Gaussians; A also labels Gaussian tests. They do not discharge the exact eta event. Translation invariance is reproduced diagnostically. |
| P_CANONICAL_CUTOFF_R1_E_POSITIVE | 0.85 | CONFIRMED_DIAGNOSTIC | The nominal explicit quintic cutoff is supplied, E is positive in both reports; not an exact-zero or universal certificate. |
| P_CANONICAL_CUTOFF_R2_E_POSITIVE | 0.90 | CONFIRMED_DIAGNOSTIC | Same scope at R=2. |
| P_POLE_NULL_TWO_BUMP_FALSIFIER_RATIO | 0.40 | UNRESOLVED | TC rejects the small bar in B and A has an error larger than the sign. L_2 for the same-named tests differs between implementations. |
| P_FALSIFIER_RANKS_ABOVE_PHASE_CONTROLS | 0.55 | UNRESOLVED_WITH_QUALITATIVE_AGREEMENT | Nominal rankings agree, but neither common exact test identity nor an accepted error enclosure exists. |
| P_INVERSE_POLYNOMIAL_ENCLOSURE_SURVIVES_INDEPENDENT_CHECK | 0.94 | CONFIRMED_BY_REPORTED_INDEPENDENT_CHECK | IC checks the actual Loewner inequalities and tail; no kernel rerun here. |
| P_HIGH_MODULATION_LARGE_CUTOFF_PROOF_SURVIVES | 0.85 | CONFIRMED_WITH_DECLARED_IMPORT | IC confirms the stated quantifiers and identifies the HS-domain import. Section 5 supplies a PAPER proof of that import. |
| P_ATOM_CONTRAST_CALIBRATION_SURVIVES | 0.93 | CONFIRMED_BY_REPORTED_INDEPENDENT_CHECK | IC checks the signs and factors; this does not assign the separate atomic measures. |

### The observer's claimed refutation changes the frozen class

P_SIGN_HOLDS_ON_TABLE, p=0.45, was registered for **support-matched pole-null tests**. P1 explicitly says that raw positive bumps and canonical cutoffs must not replace that class in scoring. The positive ordinary bumps are not pole-null. The canonical cutoffs are not pole-null and do not have the prescribed small support. The only supplied semilocal pole-null triple remains unresolved in TC.

Therefore the frozen p=0.45 event is **UNRESOLVED**, not REFUTED. The broader claim about all raw support-matched tests is contradicted by the reported table, but that is a different event. Neither the table nor this audit proves the pole-null assertion false. This correction does not erase the old fixed-S global-radical counterexample.

Likewise, the strongest claim that N is three orders too small depends on the normalization and the particular bump. It is not an estimate uniform over narrow tests. A and B use somewhat different profiles even before the unresolved derivative-bump discrepancy. Their substantial operator defects and estimated error bars must not be treated as certified continuum enclosures.

## 2. Q1(a): the phase class, exactly

**Lemma 1. [ABSTRACT][PAPER]** Fix

\[
 0<\delta<\delta_*:=\tfrac12(\log3-a),\quad
 I_\pm=\pm a/2+(-\delta,\delta),
\]

and define

\[
 \mathcal C_{-,\delta}
 =\{A_-h:=U_{a/2}h-U_{-a/2}h:
                    h\in C_c^\infty(-\delta,\delta;\mathbb C)\}.
 \tag{1}
\]

Then the support diameter is less than log 3, the lobes are disjoint, and

\[
 A_-=-U_{-a/2}(I-U_a),\quad
 \|A_-h\|^2=2\|h\|^2,\quad C_{A_-h}(a)=-\|h\|^2.
 \tag{2}
\]

Its L2 closure is the anti-diagonal graph on L2(I_-) direct-sum L2(I_+): the two restrictions are negatives after translation by a. It is the -1 eigenspace of the **lobe-swap involution on this two-lobe space**. It is not the -1 eigenspace of U_a on the full line: a nonzero L2 translation eigenfunction would have periodic modulus and infinite norm. It consists of globally odd functions only when h itself is even. It is a proper closed two-lobe subspace, not all odd tests.

**Proof.** The supports are disjoint because 2delta<a. Expanding the norm and the correlation at a leaves only the matching cross-lobe product. The displayed operator identity follows by multiplying the two translations. The lobe identification with a direct sum carries A_-h to (-h,h); swapping the two coordinates changes its sign. This proves all assertions. No spectral theorem about the Weil form is used. QED.

### The prime weight is not an innocuous rescaling

The actual Euler factor is B=I-rU_a with r=1/sqrt(2), not I-U_a. On all of L2, B is invertible by the geometric series, so its range is all of L2. On a fixed compact input interval its range is a graph with amplitude ratio r, not the anti-diagonal ratio 1. An overall scalar cannot change that ratio. Thus the assertion “range of I-U, i.e. weighted B-images” is false as an object identification.

### Pole conditions are independent of ordinary antisymmetry

For v_theta=(U_{a/2}h+e^{i theta}U_{-a/2}h)/sqrt(2H), H=||h||^2>0,

\[
 A_\pm(v_\theta)
 =\frac{e^{\pm a/4}+e^{i\theta}e^{\mp a/4}}{\sqrt{2H}}A_\pm(h).
 \tag{3}
\]

Neither factor in the numerator can vanish for real theta, because its two summands have unequal absolute values. Consequently v_theta is pole-null if and only if h is pole-null. Raw positive even h in the antisymmetric combination has A_+=-A_- up to sign, not A_+=A_-=0; its pole term is strictly negative. Therefore e(v)<=0 implies L_2(v)>=n(v), but Q(v)>=n(v) additionally requires e(v)<=P_02(v). These are not interchangeable.

The useful nonempty subspace is

\[
 \mathcal C_{-,\delta}^{00}
 =A_-\{h\in C_c^\infty(-\delta,\delta;\mathbb C): A_+(h)=A_-(h)=0\}.
 \tag{4}
\]

It is infinite-dimensional. Explicit inputs are h=(partial_x^2-1/4)eta_delta and its finite linear combinations with other compact bumps. Two integrations by parts prove both moments vanish. The constant-coefficient differential operator is injective on compactly supported smooth functions, since its homogeneous solutions are linear combinations of exp(x/2), exp(-x/2). Also int A_-h=0 automatically. No claim that this subspace is dense in the full Weil test class is made.

## 3. Q1(b): all three phase-dependent contributions, not just the prime

**Lemma 2. [ABSTRACT][PAPER]** Let h be real, even, nonzero and supported in (-delta,delta), with delta as in Lemma 1. Put H=||h||^2 and

\[
 A_0=\frac{\mathcal D(h)-c_AH}{H},\qquad
 J_a(h)=\frac1H\int_{a-2\delta}^{a+2\delta}a_\infty(t)C_h(t-a)\,dt.
\]

Then

\[
 J_a(h)=\frac1H\sum_{j\ge0}e^{-(2j+1/2)a}
       \left|\int h(x)e^{(2j+1/2)x}\,dx\right|^2\ge0,
 \tag{5}
\]

and the normalized phase family satisfies

\[
 C_{v_\theta}(a)=\tfrac12\cos\theta,\qquad
 \mathcal D(v_\theta)=\frac{\mathcal D(h)}H-J_a(h)\cos\theta,
\]
\[
 L_2(v_\theta)=A_0-(J_a(h)+w)\cos\theta.
 \tag{6}
\]

In particular their norms agree, but their archimedean energies need not agree.

**Proof.** Expansion of the autocorrelation gives
C_v(t)=C_h(t)/H + cos(theta)[C_h(t-a)+C_h(t+a)]/(2H).
Only the term centered at a contributes on t>0 outside the original central correlation support. Substitute into D(v)=2 int a_inf(t)(||v||^2-C_v(t))dt. At t=a only the cross-lobe term survives. All other powers of 2 are inactive because a+2delta<log3<2a. This proves (6). Expanding a_inf(t)=sum_{j>=0} exp(-(2j+1/2)t), which converges uniformly on the integration interval away from zero, gives (5). The Laplace transform of the real autocorrelation is the product of the two opposite Laplace moments; evenness makes them equal. Absolute convergence follows from 2delta<a. QED.

For the exact pole-null input h=(partial^2-1/4)eta_delta, the j=0 term of (5) vanishes, but the j=1 term is strictly positive: its moment is ((5/2)^2-1/4) times the positive eta moment. Thus the equality of D for all three of the specified pole-null phases is **not an exact identity**. The difference can be very small and hidden by rounding. TA's ordinary two-bump archimedean columns already show a visible phase difference. TB's printed repeated D entries cannot establish the false identity.

### The positive trace changes with the phase too

Let Z=T_h S_{2,1}, which is Hilbert--Schmidt by section 5. Set

\[
 n_0=\|Z\|_{HS}^2/H,\qquad
 \nu_a=H^{-1}\Re\langle U_{a/2}Z,U_{-a/2}Z\rangle_{HS}.
\]

All source operators preserve real functions, so the mixed inner product is real for real h. Expansion of the Hilbert--Schmidt square gives

\[
 n(v_\theta)=n_0+\nu_a\cos\theta,\qquad |\nu_a|\le n_0,
\]
\[
 \boxed{e(v_\theta)=n_0-A_0+(\nu_a+J_a(h)+w)\cos\theta.}
 \tag{7}
\]

There are three contributions to the phase coefficient: the Sonin mixed term, the archimedean mixed term, and the prime atom. Pair-of-projections theory does not set the sign of their sum. For complex h the same expansion is a Hermitian two-by-two form with the appropriate complex mixed term; one must retain its sine contribution rather than apply the real-even formula blindly.

For the minus phase the **first unproved inequality** is therefore

\[
 \boxed{n_0-\nu_a\le A_0+J_a(h)+w.}
 \tag{8}
\]

For pole-null h this is exactly Q(v_minus)>=n(v_minus). No proof of (8) for every such h at lambda=1 is supplied by the table or by a single Halmos block. This is the precise remaining sign, with all independent terms retained.

### An explicit finite-packet budget remains available

Let P0=S_{infinity,1}, H0=ran P0 and

\[
 G=P_0B^*BP_0|_{H_0}=(1+r^2)(I-qA),\quad
 A=\tfrac12P_0(U_a+U_{-a})P_0|_{H_0},\quad q=\frac{2r}{1+r^2}<1.
\]

For integer d>=0 define

\[
 R_d=\frac1{1+r^2}\sum_{j=0}^{2d+1}q^jA^j,\quad
 \epsilon_d=\frac{q^{2d+2}}{(1-r)^2},\quad C_v=T_vB|_{H_0}.
\]

The scalar geometric identity on spectrum(A) subset [-1,1] proves

\[
 R_d\le G^{-1}\le R_d+\epsilon_dI,
\quad n_d(v):=\operatorname{Tr}(C_vR_dC_v^*)\le n(v)
\le n_d(v)+\epsilon_dm(v),\quad m(v)=\|C_v\|_{HS}^2.
 \tag{9}
\]

On any fixed packet v_i=A_-h_i in (4), polarize all forms. The sufficient matrix condition is

\[
 \mathbf N_d+\epsilon_d\mathbf M-\mathbf L_2
          +\delta_{\rm eval}I\preceq0.
 \tag{10}
\]

Here delta_eval is a separately proved operator-norm enclosure for the finite-space, quadrature and representation errors. For nonorthonormal packet coordinates use a coefficient-norm error or carry the exact Gram matrix; do not call a coordinate-dependent error a physical norm bound. A list of negative diagonal entries does not establish (10). No matrix (10) was run here, and the old inverse tail does not bound the observed carrier-model error automatically.

For clarity, the existing finite-space tail can be kept explicit. If F_M is an orthogonal finite-rank projection on H0 and tau_M(v)=||C_v(I-F_M)||_HS, the sandwich replacement error for either G^(-1) or R_d is bounded by

\[
 (1-r)^{-2}\{2\sqrt{m(v)}\,\tau_M(v)+\tau_M(v)^2\}.
 \tag{10b}
\]

This follows by expanding C_v=C_vF_M+C_v(I-F_M) and applying the Hilbert--Schmidt Cauchy--Schwarz inequality to the two cross terms. For all packet coefficients simultaneously, use a proved operator-norm bound for the corresponding polarized tail matrix. Quadrature and source-carrier errors remain separate addends in delta_eval.

## 4. Q1(c)--(d): cutoff, narrow traces and the false local factor

### Cutoff placement does not act on the support of the convolution test

For every c,

\[
 T_{U_cv}=U_cT_v,\qquad n(U_cv)=n(v),\qquad e(U_cv)=e(v).
 \tag{11}
\]

The first equality is convolution algebra; unitarity proves the norm equality, and L_2 is translation-invariant. Thus putting the support of v entirely in x<=0 cannot cause its Sonin trace to vanish. The position projection acts on the argument of T_v, not on v as an input vector.

In fact n(v)>0 for every nonzero smooth compact v. Its Fourier transform is entire and nonzero almost everywhere on the real line, so convolution T_v is injective on L2. Sonin's space is nonzero; therefore T_v cannot annihilate all of it. This establishes strict positivity, not a useful uniform lower bound.

The exact independently bounded expression is

\[
 n(v)=\operatorname{Tr}(C_vG^{-1}C_v^*),\qquad
 \frac{n_\infty(Bv)}{(1+r)^2}\le n(v)
 \le\frac{n_\infty(Bv)}{(1-r)^2}.
 \tag{12}
\]

Hence the tiny value for a particular smooth profile reflects the action of its convolution multiplier on the Sonin range, not automatic support annihilation. The table alone does not prove a uniform narrow-bump collapse or identify an asymptotic law. The raw profiles and their norms also vary with b.

Unequal cutoffs do not provide an extra parameter at fixed product: U_c sends (T,W) to (e^cT,e^(-c)W), and conjugates both projections and Sonin. T_v commutes with U_c. Consequently n and e depend on T,W only through TW in this common model. Merely moving the cutoff center does not repair a sign.

As a common lambda increases, Sonin ranges decrease; hence n_lambda(v) and e_lambda(v)=n_lambda(v)-L_2(v) decrease. Decreasing lambda below 1 increases them. It may enlarge the positive trace, but makes the desired minorant n<=L_2, or n<=Q, harder, not easier. In particular whenever L_2(v)<0, e_lambda(v)>0 for every finite cutoff. Many raw symmetric table rows have exactly this obstruction. There is no cutoff trick converting those negative L_2 values to a minorant without the pole correction.

### An explicit plant, with its scope declared

Use the same false local multiplier as P0:

\[
 M_p(s)=(1-p^{3/4-s})(1-p^{-1/4+s}),\quad p=2,
\]

whose centered zero lattices have real parts +/-d with d=1/4. Keep the actual Sonin positive object fixed and change the arithmetic side by this factor. This is a test of an alleged arithmetic identification, **not** a claim that there is a new local field with a corresponding Sonin pair.

Its additional log Weil form is, for compact v,

\[
 Q_M(v)=2a\|v\|^2+4a\sum_{j\ge1}\cosh(dja)C_v(ja).
 \tag{13}
\]

To verify this without RH, the zeros of the two elementary exponential factors are explicitly +/-d+2pi i k/a. Poisson summation for their two known lattices evaluates the autocorrelation at ja, giving (13), including the j=0 mass 2a. Equivalently expand their logarithmic derivatives on their respective half-planes and match the constant term. This uses only the explicit artificial factors, not unknown zeta zeros.

For v_theta above only j=1 survives, so

\[
 Q_M(v_\theta)=2a+2a\cosh(a/4)\cos\theta.
\]

Define L_sharp=L_2+Q_M and e_sharp=n-L_sharp. Then

\[
 \boxed{e_{\rm sharp}(v_-)=e(v_-)+\delta_M,
 \qquad\delta_M=2a(\cosh(a/4)-1)>0.}
 \tag{14}
\]

The minus phase remains negative under this plant precisely when its original negative margin exceeds delta_M. No statement “the sign survives on the whole phase class” is proved. A finite observed margin may survive the plant; a direction sufficiently near zero will not. The normalized raw b=0.1 rows suggest survival, registered below as a prediction, not a computation here.

Even survival would show only that this particular phase-sign test does not distinguish the artificial factor. It would not prove that the whole class or the actual mechanism is purely archimedean. Formula (7) retains a genuine prime coefficient as well as two other phase-dependent terms.

## 5. Q2(a)--(b): compact angles, divergent bare square sum, and ordinary tested traces

### 5.1 The exact one-prime compression

**Theorem 3. [ABSTRACT][PAPER]** For every prime p and every finite lambda>0, let F_p be the literal one-prime Fourier involution and

\[
 A_{p,\lambda}=P_\lambda F_pP_\lambda|_{\operatorname{ran}P_\lambda}.
\]

Then

\[
 A_{p,\lambda}\text{ is compact},\qquad
 A_{p,\lambda}\notin\mathfrak S_2,\qquad
 A_{p,\lambda}\in\mathfrak S_q\ (q>2).
 \tag{15}
\]

Here S_q denotes the Schatten class, not a Sonin projection. In particular A and the parent's angle operator D_S are not trace class without a test.

**Proof of compactness and explicit tail.** Write a_p=log p, r_p=p^(-1/2). The exact finite Euler intertwiner gives

\[
 F_p=\mathcal U_pF_\infty,\qquad
 \mathcal U_p=(I-r_pU_{a_p})(I-r_pU_{-a_p})^{-1}
 =(1-r_p^2)\sum_{j\ge0}r_p^jU_{-ja_p}-r_pU_{a_p}.
 \tag{16}
\]

This is a norm-convergent series of bounded operators. Every compressed shifted cosine transform is Hilbert--Schmidt on the physical square (0,lambda)^2, hence compact. Truncating the sum at j=J gives A^(J) with

\[
 \|A-A^{(J)}\|\le\rho_J:=(1+r_p)r_p^{J+1}.
 \tag{17}
\]

Thus A is compact. Unitarity and self-adjointness follow from the exact unimodular multiplier and its reflection symmetry, not from the inexact finite carrier. The common time/Fourier support intersection is zero, as in P0: the finite Euler intertwiner and its inverse preserve the lower log half-line, reducing this intersection to the ordinary compact-support uncertainty statement. Hence ||A||<1, since a compact compression attaining norm 1 would produce a nonzero intersection vector.

**Proof of non-Hilbert--Schmidt.** In physical coordinates the distributional kernel on (0,lambda)^2 is

\[
 \boxed{K_p(u,v)=2(1-p^{-1})\sum_{j\ge0}\cos(2\pi p^juv)
                    -\frac2p\cos(2\pi uv/p).}
 \tag{18}
\]

The missing geometric coefficient in each cosine is not a typo: the factor r_p^j is canceled by the Jacobian factor of the unitary log shift. The series must be read as a distribution, not a pointwise convergent function. It agrees with the norm-convergent operator (16); on a compact rectangle away from the axes this follows by integration by parts in u against smooth tests.

Suppose K_p were locally L2 on such rectangles, as it would be if A were Hilbert--Schmidt. The smooth change (u,v)->(u,z=uv), followed by integration against a compact u-test on a product subrectangle, would make

\[
 \Sigma(z):=\sum_{j\ge0}\cos(2\pi p^jz)
\]

locally L2 on an open interval I subset (0,lambda^2). Choose chi in C_c^infinity(I) with int chi !=0. Then chi Sigma would be L1, and its Fourier transform would tend to zero. But at frequency 2pi p^k,

\[
 \widehat{\chi\Sigma}(2\pi p^k)\longrightarrow\tfrac12\int\chi\ne0.
\]

Indeed the resonant j=k positive frequency gives exactly the displayed term. For j<k all nonresonant frequency differences have magnitude at least (1-1/p)p^k, giving O(k p^(-kM)) for every M; j>k is bounded by a convergent O(sum_{j>k}p^(-jM)); the negative frequencies are equally harmless. This contradicts Riemann--Lebesgue. The finite smooth last term in (18) does not affect the argument. Therefore A is not Hilbert--Schmidt.

**Proof of the upper Schatten bounds.** The j-th weighted compression r_p^j P U_{-ja_p} F_infinity P has operator norm <=r_p^j and Hilbert--Schmidt norm <=2lambda. Interpolation of singular values gives its S_q norm at most (2lambda)^(2/q) r_p^(j(1-2/q)). Summing for q>2 and bounding the single remaining shifted term proves

\[
 \|A\|_{\mathfrak S_q}\le B_q(p,\lambda)
 :=(2\lambda)^{2/q}
 \left(\frac{1-r_p^2}{1-r_p^{1-2/q}}+1\right)<\infty.
 \tag{19}
\]

The complete angle decomposition has two singular values |alpha_n| on each nontrivial D_S block, with eigenvalues +/-|alpha_n|; the other subspaces contribute zero to D_S. Thus the same Schatten conclusions hold for D_S. QED.

In particular the table's suggested nonzero limiting plateau cannot be the true infinite tail. Conversely, a 1/n decay is also impossible: it would be square summable. The evidence and the theorem are compatible with a long finite plateau followed by a critical slow tail, not with either an actual nonzero accumulation point or a prolate-like summable tail.

### 5.2 Smoothing by the test closes the missing trace-domain obligation

**Theorem 4. [ABSTRACT][PAPER]** For every smooth compact log test f, every fixed finite cutoff, and one prime p, each of

\[
 T_f(I-P-Q),\qquad T_f\mathsf S_p,\qquad T_fD_S
\]

is trace class in the ordinary sense. Therefore the split and the absolutely convergent **tested** weighted angle-energy formula survive without an additional renormalized trace. This also holds for any fixed finite prime set, by the same finite-product proof.

**Trace-class lemma.** If h is a Schwartz convolution kernel and P_b is multiplication by 1_{x<=b}, then [C_h,P_b] is trace class. Also C_h 1_I is trace class for a bounded interval I. To see the first assertion, its two off-diagonal blocks have kernels h(plus-or-minus(x+y)), x,y>0, after translation/reflection. Partition both half-lines into unit intervals. On each unit square, two integrations by parts in each variable in a cosine basis bound the matrix coefficients by a constant times (1+n)^(-2)(1+m)^(-2), with a factor decaying faster than any power of the sum of the interval indices. The absolute sum over n,m and the interval indices is finite. This is an explicit sum of rank-one operators with summable trace norms. The bounded-interval assertion has the same proof; for compact h there are only finitely many squares, and for Schwartz h the outer-square sum decays. Boundary terms in the integrations by parts are retained and satisfy the same coefficient bounds. This proves the lemma; C20 Lemma D.1 gives the matching standard commutator result.

Work now on the log line. Let reflection be Rg(x)=g(-x), and let C_m denote the unitary Fourier multiplier in F_p=C_m R. Its symbol is

\[
 m(\tau)=m_\infty(\tau)
       \frac{1-r_pe^{-i\tau a_p}}{1-r_pe^{i\tau a_p}}.
\]

The archimedean gamma quotient is smooth on the real line and all its derivatives have at most polynomial growth (its logarithmic derivative has logarithmic growth, by the gamma asymptotics). The periodic rational Euler factor and all its derivatives are bounded, since 1-r_p>0. Consequently hat(f)m is Schwartz whenever f is smooth compact. If b=log lambda,

\[
 R_0:=I-P_b-F_pP_bF_p
   =C_mP_{-b}C_m^*-P_b
   =[C_m,P_{-b}]C_m^*+(P_{-b}-P_b).
\]

Multiplication by T_f gives

\[
 T_f[C_m,P_{-b}]
   =[T_fC_m,P_{-b}]-[T_f,P_{-b}]C_m.
 \tag{20}
\]

The commutators are trace class by the lemma, since their convolution symbols are Schwartz. The interval term T_f(P_-b-P_b) is trace class as well. Thus T_f R_0 is trace class, independently of any trace formula or positivity assertion.

For the archimedean pair, P_lambda F_infinity P_lambda has kernel 2cos(2pi uv) on a compact rectangle. Its Taylor series is a sum of rank-one kernels with trace norms summing to at most 2lambda cosh(2pi lambda^2), so it is trace class independently of any spectral asymptotic. Its angle operator D_infinity is trace class. Hence T_f S_infinity=T_f R_infinity+T_f D_infinity is trace class.

Finally, C23 and the independently positive Gram inverse give

\[
 \mathsf S_p=B\mathsf S_\infty G^{-1}\mathsf S_\infty B^*,\qquad
 G\ge(1-r_p)^2I>0.
\]

Since T_f commutes with B,

\[
 T_f\mathsf S_p=B(T_f\mathsf S_\infty)
                       G^{-1}\mathsf S_\infty B^*
\]

is trace class. Subtracting T_f R_0 proves T_f D_S trace class. No assertion that untested D_S is trace class was used. QED.

**Consequences for the request.** The identities (3)--(9) of P0 and the weighted formula (3) of P1 hold after testing. For f=v*v^*, positivity of T_f and the orthonormal D_S eigenbasis imply absolute convergence of
sum |alpha_n| (||T_v e_n^+||^2+||T_v e_n^-||^2): these are the absolute diagonal entries of the trace-class operator T_f D_S. This proves the needed domain for that formula. It does not prove pointwise convergence of the untested epsilon_n(rho) distributional series.

The source's log(TW)f(1) contact remains exactly as printed in C26 (22); in e it has the opposite sign. There is no freedom to add a new contact constant. Separately tracing I, P, Q or D before testing is not legitimate. Rough-grid substitution requires its own uniform error bound and is not licensed by Theorem 4. Thus the large direct-E errors in TA/TB are not evidence that the correct tested trace fails to exist.

### 5.3 A direct check that the tested trace retains the exact prime atom

**Lemma 5. [ABSTRACT][PAPER]** In the same model, with equal cutoffs for the archimedean and one-prime pairs,

\[
 \boxed{\operatorname{Tr}\bigl(T_f(R_p-R_\infty)\bigr)
 =-a_p\sum_{j\ge1}r_p^j\{f(ja_p)+f(-ja_p)\}.}
 \tag{21}
\]

This computes the difference of the full tested trace expressions; it does not separately assign prime atoms to Sonin and angle terms.

**Proof.** The Euler unitary C=U_p in (16) has an absolutely summable shift expansion with summable first shift moment. Set Q_infinity=F_infinity P F_infinity. Then R_p-R_infinity=Q_infinity-CQ_infinity C^*. Conjugating by F_infinity, and using F_infinity C F_infinity=C^*, reduces its tested trace to
Tr(T_(f reflected) [P,C^*]C).
For finite shift sums the elementary kernel calculation is

\[
 \operatorname{Tr}(T_f[P,U_d]U_e)=-d\,f(-d-e).
\]

Indeed P-U_d P U_-d is a signed interval indicator of integral -d, and the convolution kernel on the diagonal is f(-d-e). The series limit is allowed in trace norm: each interval term is bounded by C_f(1+|d|), by partition into unit intervals and the lemma above, and the first shift moment is summable.

In Fourier notation this trace is

\[
 \frac{i}{2\pi}\int\widehat f(-\tau)\frac{c'(\tau)}{c(\tau)}d\tau,
\quad c(\tau)=\frac{1-r_pe^{-i\tau a_p}}{1-r_pe^{i\tau a_p}}.
\]

But c'/c=2i a_p sum_{j>=1} r_p^j cos(j a_p tau), with absolute uniform convergence. Fourier inversion proves (21). The j>J first-moment tail is explicitly

\[
 (1+r_p)r_p^{J+1}
 \left(1+a_p(J+1)+\frac{a_pr_p}{1-r_p}\right).
\]

It controls the shift-commutator truncation up to the specified test-dependent trace-norm constant. No zero sum or RH input appears. QED.

## 6. Q2(c): what can actually be predicted about the spectrum

Let s_n=|alpha_n| be ordered nonincreasingly for the true compression. Theorem 3 proves

\[
 s_n\to0,\quad \sum s_n^2=\infty,\quad
 s_n\le B_q n^{-1/q}\quad(q>2).
 \tag{22}
\]

Thus every exponent beta<1/2 gives an O(n^(-beta)) upper bound, while no exponent beta>1/2 can give such an upper bound. This is a **critical Schatten threshold**, not a proved asymptotic s_n~C/sqrt(n), nor a pointwise lower bound. Signed alpha_n need not alternate as in the prolate example. A power-law fit must use sorted singular values of a self-adjoint source compression, not eigenvalues of the non-self-adjoint carrier surrogate.

### A source-defined finite evaluator with a norm tail

For a target tau>0 choose J so that rho_J in (17) is at most tau/10. This integer is given explicitly by

\[
 J\ge\left\lceil\frac{\log(10(1+r_p)/\tau)}{\log(1/r_p)}\right\rceil-1.
 \tag{23}
\]

Compute only the finite smooth kernel A^(J) on (0,lambda), then attach both its quadrature enclosure delta_J and the analytic tail rho_J. Weyl's singular-value inequality supplies

\[
 |s_n(A)-s_n(A^{(J)})|\le\rho_J,
\quad
 \#\{s_n(A^{(J)})>\tau+\rho_J\}
 \le n_\lambda(\tau)
 \le\#\{s_n(A^{(J)})>\tau-\rho_J\},
 \tag{24}
\]

with thresholds widened by delta_J for a numerical approximation. Unrepresented finite-kernel spectral tails must also be bounded, not silently set to zero.

There is an explicit Hilbert--Schmidt upper bound for the count. Put b_-1=p^(-1), c_-1=-p^(-1), and b_j=p^j,c_j=1-p^(-1) for 0<=j<=J. Let

\[
 I_\lambda(t)=\begin{cases}
 \operatorname{Si}(2\pi t\lambda^2)/(2\pi t),&t\ne0,\\
 \lambda^2,&t=0.
 \end{cases}
\]

Product-to-sum and two elementary integrations give

\[
 H_J^2:=\|A^{(J)}\|_{HS}^2
 =2\sum_{j,k=-1}^Jc_jc_k
          \{I_\lambda(b_j-b_k)+I_\lambda(b_j+b_k)\}.
\]

Hence, for tau>rho_J,

\[
 \boxed{n_\lambda(\tau)\le H_J^2/(\tau-\rho_J)^2.}
 \tag{25}
\]

These formulas specify a finite calculation; none was evaluated here. They remove the claim that a uniform physical carrier of enormous length is the only possible computational representation.

At tau=10^(-6), the true count is finite for every fixed lambda. It cannot increase indefinitely in a family converging in operator norm, except for a threshold-equality ambiguity. The existing grid has dim ran P approximately floor(lambda sqrt(2N))+1, so its reported count is also censored by that finite rank. The present 40--78 block counts do not estimate the continuum count with a proved error. A fixed near-0.4 plateau extending to arbitrarily many resolved singular values would contradict (22), but the current source/polar norm discrepancy excludes that premise.

### Registered numerical forecasts, not asymptotic theorems

All probabilities below precede any new calculation by this judge. They do not precede the supplied tables. The pre-write branch check exposed the title of post-request commit 8c3615f02a131c710193e03b3c548ae373ee5b24 about carrier-dependent angle counts; its report and data were not read. No claim is made that these forecasts precede other agents' new runs, and that title is not used as mathematical evidence. Tests are conditional on the explicit resolution gates; if those gates fail, score UNRESOLVED, not success.

```yaml
P_CRITICAL_HALF_POWER_WINDOW:
  probability: 0.65
  algorithm: >-
    Use the source kernel (18) truncated by (23), with certified total norm
    error below 0.05 times the smallest singular value used. For n at least
    32, discard the leading near-one cluster. On a resolved doubling block,
    compare the median of s_(2k)/s_k for n<=k<2n.
  event: median_ratio_between_0_55_and_0_85
  scope: diagnostic_intermediate_asymptotic_not_a_uniform_law
  fate: PENDING
P_COUNT_THRESHOLD_QUADRATIC:
  probability: 0.60
  parameters: p2_lambda1_tau_in_1e-2_5e-3_2_5e-3
  gate: counts_not_rank_censored_and_total_norm_error_below_tau_over20
  event: successive_n_tau_over2_div_n_tau_between_2_5_and_5_5
  fate: PENDING
P_COUNT_LAMBDA_QUADRATIC:
  probability: 0.55
  parameters: p2_lambda1_and_lambda2_tau1e-2
  gate: both_counts_certified_not_rank_censored
  event: count_lambda2_div_count_lambda1_between_2_5_and_5_5
  fate: PENDING
P_RAW_CARRIER_NEXT_COUNT_GROWS_WITH_RANK:
  probability: 0.70
  parameters: original_B_carrier_p2_lambda1_tau1e-6_N8192_to16384
  gate: same_source_variant_same_rank_threshold_no_new_symmetrisation
  event: next_count_div_N8192_count_between_1_15_and_1_65
  interpretation: finite_carrier_diagnostic_only_not_continuum_asymptotics
  fate: PENDING_NO_RUN_AUTHORISED
```

The last row predicts one as-yet-unread larger carrier, not the already supplied 4096-to-8192 comparison. It is a prediction about that imperfect instrument, not a claim of continuum convergence. All four are new extrapolations from the supplied evidence. No exact exponent or coefficient is inferred from two large leading angles, and no larger run is authorised by this document.

## 7. Q3: R1 retained, but only with honest class and quantifiers

The repaired target is fixed in advance:

\[
 S=\{\infty,2\},\quad T=W=1,\quad
 \delta_0=(\log3-\log2)/8,
\]
\[
 \boxed{\forall h\in C_c^\infty(-\delta_0,\delta_0;\mathbb C),\quad
 A_+(h)=A_-(h)=0\Longrightarrow
 n(A_-h)\le L_2(A_-h).}
 \tag{R1-}
\]

This is an infinite-dimensional, nonempty pole-null two-lobe class with support diameter a+2delta0<log3. A proof would give a Thm-7.1-type minorant on that exact class with its lobe constraint and pole constraints. It would not establish the full log-3 class, even-simple ground states, or global Weil positivity. There is no density assertion that discards the lobe relation.

For real even h the missing sign is (8); for general complex h it is the polarized version of (10). The numerical v_minus rows do not prove R1-, and the unresolved pole-null triple does not refute it. Retaining the target is a research decision based on an explicit structure, not a conclusion that its sign is known.

Two concrete representations remain useful without adding free premises to a purported completed theorem. First, the exact mixed phase form (7) isolates the necessary Sonin cross term. Second, the positive Gram inverse (9) computes that term with a one-sided tail on a finite packet. The Euler/lacunary representation (18) is an independent source check for the underlying pair. None permits omitting the infinite packet limit.

What is closed as a proposal is the claim that the **bare all-test fixed-S minorant** follows from the observed phase ordering or from a one-block sign. The prior global-radical counterexample remains in force. It is not a counterexample to (R1-) because the canonical cutoffs are outside its class.

## 8. Observer scoring, new checks and next decisive action

| Frozen SEMITABLE forecast | p | Fate | Reason |
|---|---:|---|---|
| P_PHASE_CLASS_IS_RANGE_OF_I_MINUS_U | 0.45 | REFUTED_AS_COMPOUND | The I-U anti-diagonal description is correct. The identification with weighted B-images and the single-block sign inference are not. No universal phase sign is claimed. |
| P_PHASE_CLASS_SURVIVES_PLANT | 0.55 | UNRESOLVED_AS_CLASS_CLAIM | Equation (14) is exact. Survival depends on the negative margin; the universal sign on R1- has not been proved. |
| P_D_S_NOT_TRACE_CLASS | 0.60 | CONFIRMED_BARE_OPERATOR; REGULARISATION_INFERENCE_REFUTED | Theorem 3 proves the stronger non-HS assertion. Theorem 4 proves ordinary trace class after a smooth test, so extra regularisation does not follow. |
| P_ANGLES_ACCUMULATE_AT_ZERO_SLOWLY | 0.50 | CONFIRMED_CRITICAL_SCHATTTEN_SCOPE; EXACT_RATE_OPEN | Equation (22) rules out a nonzero accumulation point and every summable faster power; it does not prove a literal asymptotic power law. |
| P_R1_RESTATED_ON_PHASE_CLASS | 0.50 | CONFIRMED | R1- is stated with fixed cutoff and exact constraints. |
| P_R1_CLOSED | 0.30 | REFUTED_AS_DECISION_FORECAST | R1- is retained. The broad invalid scope is not substituted for it. |

Additional judge forecasts for independent verification:

```yaml
P_LACUNARY_NON_HS_PROOF_SURVIVES:
  probability: 0.87
  event: theorem3_survives_without_weakening_compact_nonHS_all_lambda
  fate: PENDING
P_SMOOTH_TRACE_DOMAIN_PROOF_SURVIVES:
  probability: 0.84
  event: theorem4_proves_ordinary_trace_class_for_every_smooth_compact_test
  fate: PENDING
P_PHASE_ARCHIMEDEAN_CROSS_TERM_RESOLVED:
  probability: 0.95
  event: same_exact_eta_derivative_test_has_strictly_positive_Ja_not_identical_D
  fate: PENDING
P_RAW_MINUS_B01_SURVIVES_FALSE_FACTOR:
  probability: 0.80
  test: >-
    B tests.py mk_two(b=0.1,sign=-1), normalized in L2; same exact test
    under the unchanged Sonin projector, replacing the arithmetic side
    by L2+QM with d=1/4 as in (13).
  event: e_sharp_is_negative_after_certified_margin_exceeds_deltaM
  fate: PENDING
```

**Cheapest decisive check:** before any larger carrier, reconcile the exact serialized base function h for the pole-null triple. Both implementations must agree on H, D(h), A_+(h), A_-(h), C_v(a), and the small but nonzero J_a(h). Check the analytic derivative of eta and the scale delta0. Use the same normalization and avoid comparing a rounded D as an exact invariant. This is cheaper than computing a Sonin trace and distinguishes the current object mismatch immediately.

After that, the next operator check is the finite source kernel A^(J) with the analytic norm tail (17), not another uncalibrated source-versus-polar comparison. No such run is authorized by this verdict. A numerical sign is admissible only from a one-sided enclosure of the exact packet matrix, including all representation errors. Finite signs do not supply the quantifier in R1-.

### Closeout

The class, its complement, the prime weight and the pole conditions are now separate and explicit. A false exact invariance of the archimedean energy has been corrected. The angle spectrum is classified rigorously at the Schatten threshold; a true nonzero plateau and a 1/n tail are both excluded. The tested trace-domain gap N1 is closed on paper without making the bare angle operator trace class. The exact prime increment is recovered in the full trace difference; separate atomic allocation to N and E remains open.

No RH-equivalent target was killed merely for that equivalence. No new numerical evidence is generated here. The current unproved sign is (R1-), with (8)--(10) as its explicit finite-packet and mixed-form representations. The proof class is narrower than the full Weil test class and is not advertised as a global closure.

Only this verdict may be written. Prior verdicts, predictions, tables, scripts, state and Lean files remain unchanged. Commit and readback receipts are reported outside the immutable document.
