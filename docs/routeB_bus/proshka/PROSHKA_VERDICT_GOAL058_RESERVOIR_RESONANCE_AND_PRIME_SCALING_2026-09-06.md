# STATUS: TRY_SOURCE_MELLIN_REMAINDER_AND_EXACT_PERIODIC_PHASE_BUDGET
```yaml
OPERATIVE_CLASS: TRY_SOURCE_MELLIN_REMAINDER_AND_EXACT_PERIODIC_PHASE_BUDGET
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-06-RESONANCE
BOUNDARY_ID: GOAL058_RESERVOIR_RESONANCE_AMPLITUDE_AND_PRIME_SCALING
RESULT:
  Q1: PARTIAL_WITH_PRECISE_REMAINDER
  Q1a: PROVED_ON_CLASS
  Q1b: PARTIAL_WITH_PRECISE_REMAINDER
  Q1c: PARTIAL_WITH_PRECISE_REMAINDER
  Q2: ATTEMPT_REFUTED_WITH_EXACT_COUNTEREXAMPLE
  Q3: PARTIAL_WITH_PRECISE_REMAINDER
  Q3a: PROVED_ON_CLASS
  Q3b: PARTIAL_WITH_PRECISE_REMAINDER
REQUEST_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  COMMIT: 3aa3a3430a09710861ebd65a304b75ff1a817732
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_RESERVOIR_RESONANCE_AND_PRIME_SCALING_2026-09-06.txt
  GIT_BLOB: afc7271739fa067a9ee81ee8d91cb6b5022c2e1c
  SHA256: 1893d5e08e8f10430c0247964f43a3b273afb4514868ab8e5ed4e85e99c05692
  BYTES: 11016
  LINES: 94
  FINAL_LF: true
  FETCHED_USING_GITHUB_CONNECTOR: true
  UTF8_SHA256_AND_GIT_BLOB_RECOMPUTED: true
  ALL_FOUR_CHECKS_MATCH: true
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
CLOSES: [REQ-2026-09-06-RESONANCE]
CLOSES_ANALYTIC_RH_SUPPLIERS: []
CLOSED_REVIEW_OBLIGATIONS:
  - fixed_prime_source_density_periodic_leading_term
  - exact_periodic_phase_mass_constraint
  - prime_uniform_bounded_times_rp_cross_term_obstruction
  - peak_notch_with_positive_three_lobe_atom
OPENS: []
REMAINS_OPEN:
  - SEMITABLE_R1_MINUS_AT_FIXED_CUTOFF_1
  - all_test_sign_of_the_Sonin_increment_on_the_minus_class
  - favourable_full_reservoir_sign_for_a_peak_notched_lobe_polynomial
  - certified_source_explanation_of_the_observed_finite_frequency_multiplets
DECISIONS:
  SINGLE_COSINE_IS_THE_FULL_LEADING_TERM: false
  ALL_FIXED_EULER_HARMONICS_PERSIST: true
  FIRST_HARMONIC_AMPLITUDE: log(p)/(pi*sqrt(p))
  ONE_PRIME_ANGLE_DENSITY_REMAINDER: O_p(abs(xi)^(-1/2))
  ARCHIMEDEAN_ANGLE_DENSITY_REMAINDER: O(abs(xi)^(-2))
  FIXED_FINITE_S_REMAINDER_CONSTANT_IS_UNIFORM_IN_S: false
  GLOBAL_POINTWISE_KINF_LE_QINF_OVER_2PI: false
  PERIODIC_PHASE_MARGINAL_DEPENDS_ON_H_SHAPE: false
  ALL_ODD_LATTICE_ZEROS_ARE_FINITE_CODIMENSION: false
  P_MINUS_ONE_ZERO_AND_FAVOURABLE_ATOM_COMPATIBLE: true
  THESE_TWO_FACTS_PROVE_FAVOURABLE_RESERVOIR_SIGN: false
  ATOM_HAS_A_UNIFORM_LOG_P_ADVANTAGE_OVER_RESONANCE: false
  WHOLE_PHASE_CLASS_SIGN_PROVED: false
  WHOLE_PHASE_CLASS_SIGN_REFUTED: false
  FALSE_LOCAL_FACTOR_WHOLE_CLASS_SURVIVAL: refuted_by_high_modulation_family
SCOPED_REFUTATIONS:
  - NAME: PRIME_UNIFORM_ABSOLUTE_CROSS_TERM_BOUND_BY_C_TIMES_RP
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: exact_asymptotic_counterexample_family_with_strict_negative_upper_bound
    EVIDENCE: this_verdict_section_4_4_equation_27
    SCOPE: ABSTRACT
    VERIFIER: PAPER
  - NAME: NONZERO_SHORT_H_WITH_ZEROS_AT_EVERY_ODD_PHASE_LATTICE_POINT
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: Fourier_completeness
    EVIDENCE: this_verdict_section_5_2
    SCOPE: ABSTRACT
    VERIFIER: PAPER
  - NAME: SPECIFIED_FALSE_LOCAL_FACTOR_SURVIVES_ON_THE_ENTIRE_MINUS_CLASS
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: strict_negative_upper_envelope_on_explicit_pole_null_family
    EVIDENCE: this_verdict_section_7_equation_36
    SCOPE: ABSTRACT
    VERIFIER: PAPER
EVIDENCE_BOUNDARY:
  CONTROLLING_PARENT_PHASEROOF_BLOB: 6f0c389971d97e7330cadad0c90cfe3af5376fb4
  CONTROLLING_PARENT_IS_THE_ONE_AT_REQUEST_COMMIT: true
  OTHER_LOCAL_PHASEPROOF_VERSION_IS_NOT_CONTROLLING: true
  POST_REQUEST_BRANCH_METADATA_SEEN: 065b437ab5a4407fcda44372b7b347efbcffea69
  POST_REQUEST_REPORTS_USED_AS_MATHEMATICAL_PREMISES: false
  OBSERVER_NUMBERS: DIAGNOSTIC_NEVER_A_PROOF
  ALL_SHELF_SHA_PREFIXES_RECOMPUTED: false
NEW_DERIVATIONS:
  SCOPE: ABSTRACT
  VERIFIER: PAPER
  INDEPENDENT_REVIEW: pending
  LEAN_KERNEL_VERIFIED: false
  HISTORICAL_NOVELTY: not_claimed
REVIEW_BOUNDARY: PAPER_PROOF_CONSTRUCTION_AND_ADVERSARIAL_REVIEW
AUTHORIZED_WRITE_SCOPE: VERDICT_DOC_ONLY
EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_RESERVOIR_RESONANCE_AND_PRIME_SCALING_2026-09-06.md
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

## 0. Decision and source boundary

The fixed-prime source has a persistent **periodic leading term**, not just one cosine. Its first harmonic has amplitude \((\log p)/(\pi\sqrt p)\). Thus the proposed missing logarithm in the reservoir is not available as a uniform advantage for the atom. There is also an exact answer to the uncertainty question: a short-support test has a uniform frequency-phase marginal before the lobe weight is inserted. Shaping the base test cannot redistribute that marginal. A three-lobe polynomial can nevertheless notch the nominal peaks and keep a positive arithmetic contribution; the explicit example is \(2+z-z^2\). None of these statements proves the remaining full phase-class sign. [ABSTRACT][PAPER]

The new source-density derivation below is a **paper proof for independent checking**, not a numerical fit or a Lean certificate. In particular, its fixed-\(S\) constants are not uniform along a growing set of primes. The question of whether every admissible minus-phase test has an adverse Sonin increment remains open. The measured doublets/triplets are not certified source features merely because the leading periodic component is genuine.

### Sources actually used

**[REQ]** is the byte-exact request at the commit and hashes in the header. The fetched UTF-8 text, including its final LF, was re-encoded and checked with SHA-256 and Git's `blob <byte-count>\0` SHA-1 convention. Both hashes and both counts match.

**[PP]** is `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_PHASE_CLASS_INEQUALITY_AND_MOLLIFIER_CROSSWALK_2026-09-06.md`, at the request commit, blob `6f0c389971d97e7330cadad0c90cfe3af5376fb4`. Its definitions, (3), (6)--(13b), and the finite-packet error boundary control this adjudication. The different locally attached PHASEPROOF version is not substituted for it. **[ST]** denotes its SEMITABLE parent, blob `80eb2189b7a9de523fb0aec1bbdaa198bb02bba2`, especially the phase formulas and the Euler Fourier kernel. Prior derivations are rechecked below, not treated as axioms.

**[DF]** is `docs/routeB_bus/phase5_codex/density_fine.py` at the request commit, blob `d515e10e065bcb162644b44d8c18c6e8f5b83509`. It was read, not run. It explicitly divides the digamma multiplier by \(2\pi\), truncates the Fourier integral at 600, and forms a finite-carrier plane-wave quadratic value. The request's carrier and Fourier-tail warnings remain in force.

**[CC20]** Connes--Consani, *Weil positivity and trace formula, the archimedean place*, arXiv:2006.13771v1, Theorem 4.7, (83)--(84), and Appendix D: tested Sonin/angle traces and the smooth-convolution half-line commutator. **[CCM23]** Connes--Consani--Moscovici, arXiv:2310.18423v2, Proposition 4.6, (57), Proposition 4.7, (58)--(59), and the following Sonin stability theorem: the finite Euler map and the corresponding Fourier intertwining. **[C26]** Connes, arXiv:2602.04022v1, Sections 7.1--7.4: the fixed-cutoff trace convention. These primary texts were opened in this audit. The derivations below, including the high-frequency estimate, are not assertions that these papers already state that estimate. The q-series/Jacobi shortcut of arXiv:2403.01247v1 is not used or reopened. No result from math/9811068v1 is needed as an additional premise.

**Normalization repair.** It is \(q_\infty\), not \(q_\infty/(2\pi)\), that equals \(2\int a_\infty(t)(1-\cos(\xi t))dt-c_A\). [DF] implements the density normalization correctly; the corresponding prose in [REQ] conflates these two quantities.

## 1. Fixed operators and the exact density decomposition

All statements in this section have scope **ABSTRACT**, verifier **PAPER**. Let \(\mathcal P\) be a fixed finite set of finite primes, \(S=\{\infty\}\cup\mathcal P\), and
\[
 a_p=\log p,\qquad r_p=p^{-1/2},\qquad
 b_S(\xi)=\prod_{p\in\mathcal P}(1-r_pe^{-ia_p\xi}).
\]
Use \(\widehat h(\xi)=\int h(x)e^{-i\xi x}dx\), with the unitary Fourier transform denoted by \(\mathcal F=(2\pi)^{-1/2}\widehat{\phantom h}\). The log-to-physical unitary sends \(g(x)\) to \(u^{-1/2}g(\log u)\). Inner products are antilinear in their first argument.

On the physical half-line let \(E:L^2(0,1)\to L^2(0,\infty)\) be zero extension, \(P=EE^*\), and \(F_\infty\) the cosine involution with kernel \(2\cos(2\pi uv)\). Write
\[
 B_S=\prod_{p\in\mathcal P}(I-r_pU_{a_p}),\quad
 F_S=B_S(B_S^*)^{-1}F_\infty,
\]
\[
 Q_S=F_SPF_S,\quad R_S=I-P-Q_S,\quad
 \mathsf S_S=\operatorname{proj}(\ker P\cap\ker Q_S),\quad
 D_S=\mathsf S_S-R_S.                                      \tag{1}
\]
The definitions are transported by the stated unitary when physical and log notation occur together. The multiplier of \(B_S\) is \(b_S\). This is the literal finite-Euler model, not an unweighted lobe map. [CCM23; PP]

The physical generalized Mellin wave
\[
 f_\xi(u)=(2\pi)^{-1/2}u^{-1/2+i\xi}
\]
satisfies, distributionally,
\[
 F_Sf_\xi=\gamma_S(\xi)f_{-\xi},\qquad
 \gamma_S(\xi)=\pi^{-i\xi}
 \frac{\Gamma(1/4+i\xi/2)}{\Gamma(1/4-i\xi/2)}
 \frac{b_S(-\xi)}{b_S(\xi)},\qquad |\gamma_S(\xi)|=1.        \tag{2}
\]
For the archimedean factor this follows by integrating \(2\cos(2\pi uv)v^{-1/2+i\xi}\) and using the gamma duplication and reflection identities. Each log shift multiplies a plane wave by its stated exponential, giving the finite factors.

Put
\[
 q_\infty(\xi)=\Re\psi(1/4+i\xi/2)-\log\pi,
\]
\[
 q_S(\xi)=q_\infty(\xi)
       -2\sum_{p\in\mathcal P}a_p\sum_{j\ge1}r_p^j\cos(ja_p\xi).
                                                               \tag{3}
\]
The series and all its fixed-order derivatives converge uniformly for fixed \(S\). Differentiating (2) gives \(\gamma_S'/\gamma_S=iq_S\).

**Lemma 1 (the exact arithmetic symbol).** If \(k_S\) is the Sonin density of [PP, Lemma 3], then
\[
 \boxed{k_S(\xi)=\frac{q_S(\xi)}{2\pi}+d_S(\xi),\qquad
 n_S(v)-L_S(v)=\int|\widehat v(\xi)|^2d_S(\xi)d\xi.}        \tag{4}
\]
Here \(d_S\) is the tested Fourier diagonal of \(D_S\), not a bare trace of \(D_S\). The function representative and its bounds are constructed in Section 2.

**Proof.** On the log line \(P=1_{(-\infty,0]}\), reflection sends \(P\) to \(I-P\), and \(F_S=C_{m_S}\mathcal R\), where \(m_S(\xi)=\gamma_S(-\xi)\). Thus
\(R_S=C_{m_S}PC_{m_S}^*-P\). The Fourier kernel of \(P\) is
\(\frac12\delta(\xi-\eta)+\frac{i}{2\pi}\operatorname{pv}(\xi-\eta)^{-1}\).
Consequently the diagonal of the difference is
\[
 \frac{i}{2\pi}\frac{m_S'(\xi)}{m_S(\xi)}
 =\frac{q_S(\xi)}{2\pi}.
\]
This calculation is made after smooth convolution; it does not subtract two infinite projection traces. Fourier inversion then identifies its test value with
\[
 L_S(v)=\mathcal D(v)-c_A\|v\|^2
       -2\sum_{p\in\mathcal P}\sum_{j\ge1}a_pr_p^jC_v(ja_p).
\]
Subtract from the tested trace of \(\mathsf S_S\). This gives (4). The half-line trace-class justification is recalled in the proof of Lemma 2. QED.

This decomposition already exposes the important scale: the **arithmetic contribution to the Sonin density has the factor \(a_p=\log p\)**. It comes from the derivative of the Euler phase, not merely from the coefficient of a shift in \(B_S\).

## 2. Q1(a)--(b): source amplitude and a direct Mellin/resolvent evaluator

### 2.1 A finite-interval representation of the angle density

Define
\[
 A_S=E^*F_SE,\quad \alpha_S=\|A_S\|,\quad
 Z_S=(I-A_S^2)^{-1}.                                      \tag{5}
\]
The letter \(Z_S\) here denotes this bounded inverse, not a zeta zero or a test operator.

**Lemma 2. [ABSTRACT][PAPER]** For fixed finite \(S\), \(A_S\) is a compact self-adjoint contraction with \(\alpha_S<1\). Define the following Mellin integrals by the convergent construction below:
\[
 u_S(\xi)=A_S(f_\xi|_{(0,1)})\in L^2(0,1),\qquad
 t_S(\xi)=\langle f_\xi,A_Sf_{-\xi}\rangle_{(0,1)}.
\]
Then the exact continuous representative in (4) is
\[
 \boxed{
 d_S(\xi)=2\Re\left\{\gamma_S(\xi)
 \left[t_S(\xi)+\langle u_S(\xi),A_SZ_S\overline{u_S(\xi)}\rangle\right]\right\}
       -2\langle u_S(\xi),Z_Su_S(\xi)\rangle .}             \tag{6}
\]
In particular,
\[
 \boxed{|d_S(\xi)|\le M_S(\xi):=
 2|t_S(\xi)|+\frac{2}{1-\alpha_S}\|u_S(\xi)\|^2.}         \tag{7}
\]
The uncut Mellin wave itself is **not** in \(L^2(0,1)\); (6) does not assume otherwise.

**Proof of the operator facts.** For one prime,
\[
 F_p=\left[(1-r_p^2)\sum_{j\ge0}r_p^jU_{-ja_p}
                     -r_pU_{a_p}\right]F_\infty.           \tag{8}
\]
This is a norm-convergent series. Every compressed shifted cosine transform is compact. Finite products give the same assertion for finite \(S\). Self-adjointness and unitarity follow from (2), or from the Euler multiplier and its reflection symmetry.

If \(\|A_S\|=1\), compactness supplies a nonzero function supported in \((0,1)\) whose \(F_S\)-transform is also supported there. But
\(F_S=(B_S^*)^{-1}F_\infty B_S^*\), and \(B_S^*\) preserves the lower log half-line. Applying \(B_S^*\) gives a nonzero ordinary function and its cosine transform both compactly supported. The entire-function uniqueness argument rules this out. Hence \(\alpha_S<1\).

For \(W_S=(E,F_SE)\), the Gram operator is
\[
 W_S^*W_S=\begin{pmatrix}I&A_S\\A_S&I\end{pmatrix}.
\]
The range projection is \(W_S(W_S^*W_S)^{-1}W_S^*\). Subtracting it from \(P+Q_S=W_SW_S^*\) gives
\[
 D_S=W_S
 \begin{pmatrix}-A_S^2Z_S&A_SZ_S\\A_SZ_S&-A_S^2Z_S\end{pmatrix}W_S^*.
                                                               \tag{9}
\]
Use \(A_SZ_S=A_S+A_S^3Z_S\), (2), and reality of \(A_S\). The two diagonal terms of (9) give the last term of (6); the two off-diagonal terms give its real part. The bound (7) uses
\(\|Z_S\|\le(1-\alpha_S^2)^{-1}\) and
\(\|A_SZ_S\|\le\alpha_S(1-\alpha_S^2)^{-1}\).

**Justification of the generalized-wave calculation.** First pair (9) with a smooth convolution square. Terms containing two factors of \(A_S\) factor through the \(L^2\) vector \(u_S\) and are ordinary Hilbert--Schmidt sandwiches. For the linear term, smooth convolution times \(PF_SP\) is trace class: write
\[
 T_hPF_SP=[T_h,P]F_SP+P T_hF_SP.
\]
The first term is a smooth half-line commutator. The second is a half-line Hankel operator because \(F_S=C_{m_S}\mathcal R\) and \(\mathcal RP=(I-P)\mathcal R\). The kernel is Schwartz: \(\widehat h\,m_S\) is Schwartz, since the derivatives of the gamma multiplier have polynomial bounds and those of the fixed Euler factors are bounded. The usual half-line smooth-kernel trace-class argument is [CC20, Appendix D], also rederived in [ST].

For (8), these trace-norm bounds grow at most polynomially in the shift; every sum \(\sum r_p^j(1+j)^k\) is finite. Thus the linear term can be evaluated term by term after testing. One may cut the Mellin integrals off at \(u=\varepsilon\) first and then pass to zero. The scalar and \(L^2\) estimates immediately below justify these limits and local uniform convergence of the scalar formulas. Fourier inversion gives (6) as a density equality almost everywhere; its continuous right side specifies the representative. No pointwise series is assigned to the bare lacunary cosine kernel. QED.

### 2.2 Explicit one-prime formulas and tails

For this subsection set \(p\) fixed, \(a=\log p\), \(r=p^{-1/2}\),
\[
 \beta_{-1}=2\pi/p,\quad c_{-1}=-1/p,\qquad
 \beta_j=2\pi p^j,\quad c_j=1-1/p\quad(j\ge0).
\]
The compressed source kernel is distributionally
\(2\sum_{j\ge-1}c_j\cos(\beta_juv)\). Define ordinary, absolutely convergent improper integrals
\[
 I(\beta,\xi)=\int_0^1v^{-1/2+i\xi}\cos(\beta v)dv,
\qquad
 J(\beta,\xi)=\int_0^1(-\log v)v^{-1/2+i\xi}\cos(\beta v)dv.
\]
Then
\[
 \boxed{
 u_p(\xi)(u)=\sqrt{2/\pi}\sum_{j\ge-1}c_jI(\beta_ju,\xi),
 \qquad
 t_p(\xi)=\frac1\pi\sum_{j\ge-1}c_jJ(\beta_j,-\xi).}       \tag{10}
\]
The second formula uses
\(\int_0^1\int_0^1F(uv)dudv=\int_0^1(-\log v)F(v)dv\), with the Mellin factors retained. These are the promised source formulas for an observer; they require no long physical carrier and no q-series/Jacobi identification.

**Lemma 3 (oscillatory estimates). [ABSTRACT][PAPER]** There is an absolute constant \(C\) such that, for \(T=|\xi|\ge2\),
\[
\begin{array}{ll}
 |I(\beta,\xi)|\le C/T,&\beta\le T/2,\\
 |I(\beta,\xi)|\le C\beta^{-1/2},&\beta>T/2,\\
 |J(\beta,\xi)|\le C/T^2,&\beta\le T/2,\\
 |J(\beta,\xi)|\le C\beta^{-1/2}(1+\log(2\beta/T)),&\beta>T/2.
\end{array}                                                   \tag{11}
\]
Also
\[
 \|I(\beta\,\cdot,\xi)\|_{L^2(0,1)}\le C
 \begin{cases}
 T^{-1},&\beta\le T/2,\\
 \beta^{-1/2}\sqrt{1+\log(2\beta/T)},&\beta>T/2.
 \end{cases}                                                  \tag{12}
\]
An implementation needing numerical constants must retain a proved constant for these bounds; an unspecified big-O constant is not an interval certificate.

**Proof.** Expand cosine into two exponentials. For \(\beta\le T/2\), put \(v=e^{-x}\). The phase derivative has magnitude at least \(T/2\). One integration by parts bounds the amplitude \(e^{-x/2}\). For \(J\), the amplitude is \(xe^{-x/2}\), which vanishes at zero; two integrations by parts give the additional \(T^{-1}\). Uniformity follows by writing the inverse phase derivative as \(T^{-1}(1\pm(\beta/T)e^{-x})^{-1}\); that last function and its first two derivatives are uniformly bounded.

For \(\beta>T/2\), substitute \(y=\beta v\), then split at \(T/2\) and \(2T\), truncating the pieces at \(\beta\) when necessary. Outside this middle interval, integration by parts uses the nonvanishing derivative of \(T\log y\pm y\). In the middle put \(y=Tz\); the potentially stationary phase has second derivative bounded away from zero on \(1/2\le z\le2\). Splitting where its first derivative has size at most \(T^{-1/2}\), and integrating by parts on the two complements, gives the elementary second-derivative bound. The amplitude \(y^{-1/2}\) cancels the square-root stationary scale, leaving an absolute bound for the integral before the exterior factor \(\beta^{-1/2}\). The extra amplitude \(\log(\beta/y)\) and its total variation cost at most a constant times \(1+\log(2\beta/T)\). The lower-end boundary terms vanish since \(y^{1/2}|\log y|\to0\). This proves (11). Finally split the \(u\)-integral at \(u=T/(2\beta)\) and integrate the two squared bounds for \(I(\beta u,\xi)\); the second part is a logarithm. This proves (12). QED.

For clarity the estimates yield explicit geometric **tail shapes**, not just a convergence assertion. Once \(\beta_{J+1}>T/2\), the tail needed for either scalar series is bounded, up to its declared constant and the prefactors in (10), by
\[
 \sum_{j>J}\beta_j^{-1/2}(1+\log(2\beta_j/T))
 =\frac{r^{J+1}}{\sqrt{2\pi}}
 \left[\frac{1+\log(2\beta_{J+1}/T)}{1-r}
              +\frac{ar}{(1-r)^2}\right].                    \tag{13}
\]
For the vector tail one may use the same expression, since \(\sqrt{1+x}\le1+x\) for \(x\ge0\). On bounded frequency intervals the analogous bound is \(O_p(r^J(1+J))\), obtained by the same integrals with bounded \(\xi\).

The inverse in (6) has the separate tail
\[
 \left\|Z_S-\sum_{j=0}^dA_S^{2j}\right\|
 \le\frac{\alpha_S^{2d+2}}{1-\alpha_S^2}.                    \tag{14}
\]
Replacing it in (6) costs at most
\(2(1+\alpha_S)\|u_S\|^2\alpha_S^{2d+2}/(1-\alpha_S^2)\).
Errors in \(A_S\), \(u_S\), \(t_S\), quadrature and the physical/log transport remain separate. The Euler operator truncation has norm tail \((1+r)r^{J+1}\). A certified \(\alpha_S<1\) can be obtained from a finite-kernel norm bound plus that tail; the theoretical strict inequality alone is not a numerical value.

### 2.3 The amplitude law

**Theorem 4. [ABSTRACT][PAPER]** At cutoff 1, for each fixed prime \(p\),
\[
 d_p(\xi)=O_p(|\xi|^{-1/2}),\qquad
 d_\infty(\xi)=O(|\xi|^{-2}),                              \tag{15}
\]
\[
 \boxed{
 k_p(\xi)-k_\infty(\xi)
 =-\frac{\log p}{\pi}\sum_{j\ge1}p^{-j/2}\cos(j\xi\log p)
       +O_p(|\xi|^{-1/2}).}                                \tag{16}
\]
Equivalently the leading term is
\[
 g_p(\theta)=-\frac{a}{\pi}
       \frac{r\cos\theta-r^2}{1-2r\cos\theta+r^2},
 \qquad\theta=a\xi.
                                                               \tag{17}
\]
This is a statement about the source, not \(\xi\to\infty\) on a fixed discrete carrier.

**Proof.** Split (10) where \(\beta_j\) first exceeds \(T/2\). The low part of \(\|u_p\|\) is \(O_p((1+\log T)/T)\); its high part is \(O_p(T^{-1/2})\), by (12) and geometric summation. Thus \(\|u_p\|=O_p(T^{-1/2})\). The corresponding low part of \(t_p\) is \(O_p((1+\log T)/T^2)\), and its high part is \(O_p(T^{-1/2})\). Apply (7). With no finite prime there is only the fixed cosine kernel: (11)--(12) give \(\|u_\infty\|=O(T^{-1})\), \(t_\infty=O(T^{-2})\), and the second assertion of (15). Subtract (4) for the two sources and sum the geometric Fourier series. QED.

A fixed finite set of \(s\) primes has the weaker but sufficient extension
\[
 d_S(\xi)=O_S\bigl((1+\log|\xi|)^s|\xi|^{-1/2}\bigr)=o_S(1).
                                                               \tag{18}
\]
Indeed expand the product of (8). Each summand has a fixed finite forward dilation and a positive-semigroup dilation by integers with prime factors in a subset of \(\mathcal P\). There are \(O_S((1+\log X)^s)\) such indices below \(X\). Splitting at dilation size \(T\), and summing (11)--(12) on geometric shells, gives the stated bound for \(t_S\) and \(u_S\). The quadratic term in (7) is smaller eventually. All constants, including \((1-\alpha_S)^{-1}\), remain dependent on \(S\). This proof supplies no simultaneous large-\(S\) estimate.

**What is meant by amplitude.** The first cosine coefficient on a complete period tends to \(-ar/\pi\); its amplitude is \(ar/\pi\), and its sine coefficient tends to zero. The \(j\)-th cosine coefficient tends to \(-ar^j/\pi\). Therefore a single cosine is not the entire leading asymptotic: the second and subsequent harmonics do not disappear as \(\xi\) grows. There is no claim that the finite-frequency envelope is monotonically increasing.

For \(p=2\), the leading maximum and minimum are exactly
\[
 g_2(\pi)=\frac{\log2}{\pi}(\sqrt2-1),\qquad
 g_2(0)=-\frac{\log2}{\pi}(\sqrt2+1).
\]
They have the phase and asymmetric peak/trough structure discussed in the request. This is not a fit to the reported heights.

### 2.4 Archimedean ordering and the multiplets

There is no global pointwise inequality \(k_\infty\le q_\infty/(2\pi)\). In fact
\[
 q_\infty(0)=-c_A<0,\qquad k_\infty\ge0,
\]
so the proposed ordering fails on a neighborhood of zero. The exact relation is (4), with the continuous, integrable correction \(d_\infty\) in (15). Moreover \(\int d_\infty=\operatorname{Tr}D_\infty=0\): the archimedean angle operator is trace class and its nontrivial blocks have paired eigenvalues \(+|\alpha_j|,-|\alpha_j|\). Thus a globally one-signed correction is impossible. Neither a small high-frequency correction nor the observed eventual-looking sign proves an all-test minorant. [ABSTRACT][PAPER]

For the one-prime unitary
\[
 c_p(\xi)=\frac{1-re^{-ia\xi}}{1-re^{ia\xi}},
 \qquad
 \frac{d}{d\xi}\arg c_p
 =2a\frac{r\cos(a\xi)-r^2}{1-2r\cos(a\xi)+r^2},           \tag{19}
\]
the phase is **minus** twice the argument of the denominator. Its derivative is maximal at phase zero and minimal at phase \(\pi\). The density contribution has the additional minus sign and is maximal at \(\pi\). The rational function (17) has one maximum and one minimum per period. It does not by itself generate a doublet or triplet.

The observed additional extrema can come from the explicit correction (6), from the carrier, or from both. The bound on the correction is a bound on its value, not an eventual count of its extrema: small rapidly varying corrections can still split a peak. Therefore the multiplets at the measured frequencies remain unclassified. The source discriminator is the difference between the measured density and (3)/(2\pi), compared with (6) with independent error bounds. [ABSTRACT][PAPER for the algebra; CONDITIONAL for the finite-carrier identification]

There is an immediate finite-carrier warning. On any fixed finite carrier, the squared norm of its plane-wave vector is constant in \(\xi\); hence \(|k_{S,N}(\xi)|\le\|S_N\|\|e_{\xi,N}\|^2\) is bounded. But \(q_\infty(\xi)\sim\log(|\xi|/(2\pi))\) is unbounded. Thus sending frequency to infinity at fixed \(N\) necessarily gives the wrong source asymptotic. Stable phase at two carrier sizes does not cure this order-of-limits defect. [FINITE_CELL][PAPER]

## 3. Q1(c): exact phase averaging, piecewise bounds, and the remaining sign

Let \(a=\log2\), \(I=(-\delta,\delta)\), \(2\delta<a\), and \(0\ne h\in\mathcal H_{00}(I)\). Write \(H=\|h\|^2\) and
\[
 W_h(\xi)=\frac{(1-\cos(a\xi))|\widehat h(\xi)|^2}{H}.
\]

**Lemma 5 (exact phase marginal). [ABSTRACT][PAPER]** For every bounded measurable \(2\pi\)-periodic function \(F\),
\[
 \frac1{2\pi H}\int |\widehat h(\xi)|^2F(a\xi)d\xi
       =\frac1{2\pi}\int_0^{2\pi}F(\theta)d\theta.          \tag{20}
\]
In particular \(\int W_h=2\pi\). This result needs only the support condition, not the pole conditions, realness or parity.

**Proof.** The Fourier coefficients of the pushforward of
\(|\widehat h|^2d\xi/(2\pi H)\) to the phase circle are the normalized autocorrelations at \(na\). They are 1 for \(n=0\) and zero for every nonzero integer \(n\), because the supports are disjoint. A finite measure on the circle is determined by its trigonometric moments; polynomial density proves that this measure is Haar measure. Equality for bounded measurable functions follows. Equivalently, for smooth compact \(h\),
\[
 \sum_{k\in\mathbb Z}\left|\widehat h\left(\frac{\theta+2\pi k}{a}\right)\right|^2=aH.
\]
QED.

Separate the two requested pieces as
\[
 A(h)=\int W_h\left(\frac{q_\infty}{2\pi}-k_\infty\right),
 \qquad B(h)=\int W_h(k_2-k_\infty).
\]
Equations (4), (17), and (20) give the exact, cancellation-preserving identities
\[
 \boxed{
 A(h)=-\int W_hd_\infty,\quad
 B(h)=w+\int W_h(d_2-d_\infty),\quad
 \mathfrak m(h)=w+A(h)-B(h)=-\int W_hd_2.}                  \tag{21}
\]
Here \(w=a/\sqrt2\). To check its coefficient directly,
\(\int_0^{2\pi}(1-\cos\theta)g_2(\theta)d\theta=w\): only the first Euler harmonic survives. The atom and the leading reservoir contribution have exactly the same normalization.

Thus the diagnosis that the explicit atom supplies the positive margin of one measured row is compatible with the data, but does not establish an independent reserve available on the whole class. At the source-symbol level that atom is already reproduced by the Sonin density; the remaining sign is the angle correction.

The requested bounds on both pieces are, with the explicit envelope (7),
\[
 |A(h)|\le\int W_hM_\infty,\qquad
 |B(h)-w|\le\int W_h(M_2+M_\infty).                         \tag{22}
\]
These are finite for every test and give universal but potentially crude bounds by \(2\pi\) times the corresponding supremum. The supremum is finite by continuity and (15). They do not replace a sign by an absolute-value estimate.

A stronger short-support bound is available for controlling the low-frequency part. Let
\[
 G_I=\begin{pmatrix}2\sinh\delta&2\delta\\2\delta&2\sinh\delta\end{pmatrix},
 \quad b_I(\xi)_\pm=\int_{-\delta}^{\delta}e^{\pm x/2}e^{i\xi x}dx,
 \quad K_{00}(\xi)=2\delta-b_I(\xi)^*G_I^{-1}b_I(\xi).
\]
Orthogonal projection off \(\operatorname{span}\{e^{x/2},e^{-x/2}\}\) gives
\(|\widehat h(\xi)|^2/H\le K_{00}(\xi)\). Both entries of \(b_I\) are explicit: \(2\sinh((\pm1/2+i\xi)\delta)/(\pm1/2+i\xi)\). For any nonnegative envelope \(M\) and any \(R>0\),
\[
 \int W_hM\le
 \int_{|\xi|\le R}(1-\cos(a\xi))K_{00}(\xi)M(\xi)d\xi
       +2\pi\sup_{|\xi|>R}M(\xi).                         \tag{23}
\]
Apply this with the two envelopes in (22). This is a same-class, same-norm budget; it does not assume that the test is the observer's bump. [ABSTRACT][PAPER]

**First unproved inequality for the resonance question:**
\[
 \int W_h(d_2-d_\infty)\ge-w
       \quad\text{for every }0\ne h\in\mathcal H_{00}(I).
                                                               \tag{R-INC}
\]
**First unproved inequality for the actual phase minorant:**
\[
 \int W_hd_2\le0
       \quad\text{for every }0\ne h\in\mathcal H_{00}(I).
                                                               \tag{R-SIGN}
\]
They are different statements. This audit neither proves (R-INC) on the whole class nor constructs a source counterexample to it. The high-frequency family in Section 4 proves \(B(h_T)\to w>0\); it does not settle all shapes at finite frequency. Positivity of \(G\), or of \(k_S\), is not a substitute for either inequality.

## 4. Q2: which primes are active, and why the logarithmic advantage fails

### 4.1 Window coverage is not autocorrelation coverage

Take lobes at \(\pm b/2\), \(b=\log p\), with base half-width \(\delta\). The autocorrelation is supported near **three** points, \(0,\pm b\), not at every point of the interval \([-b-2\delta,b+2\delta]\).

For an unrestricted test class of diameter \(D\), using all finite primes at most \(e^D\) gives the usual semilocal arithmetic equality. For this constrained two-lobe class, a prime can be inside that outer window and still have identically zero autocorrelation. In particular, the statement that prime 2 *must* contribute to the lobe pair across \(\log3\) is false. It is legitimate to choose the larger \(S\), but its Sonin projector must then remain the larger one. [ABSTRACT][PAPER]

The precise small-window conditions are:

| Lobe separation | Next prime-power cutoff | Additional condition to leave only the atom at \(p\) active | Full-window finite primes |
|---|---|---|---|
| \(\log3\) | \(2\delta<\log(4/3)\) | none beyond this and the central-gap condition | \(2,3\) |
| \(\log5\) | \(2\delta<\log(7/5)\) | \(2\delta<\log(5/4)\), to exclude the nearby atom at 4 | \(2,3,5\) |
| \(\log7\) | \(2\delta<\log(8/7)\) | none beyond this and the central-gap condition | \(2,3,5,7\) |

The central-gap condition is \(2\delta<\log2\); disjointness of the two lobes is also required. All these conditions hold at the frozen \(\delta_0=(\log3-\log2)/8\). Thus only the atom at \(p\) is active for each of the three specified lobe pairs at that width. For \(p=5\), merely excluding 7, without the additional previous-power condition, is not sufficient to discard 4.

For a larger chosen \(S\), \(B_S\) and its Gram inverse still contain every chosen Euler factor, even when that factor's direct arithmetic autocorrelation is zero. This distinction prevents an unnoticed source-projector substitution.

### 4.2 Exact phase law with all potentially active atoms

For real even \(h\), define
\[
 v_\theta=\frac{U_{b/2}h+e^{i\theta}U_{-b/2}h}{\sqrt{2H}},
 \quad A_0=\mathcal D(h)/H-c_A,
\]
\[
 J_b(h)=\frac1H\int_0^\infty a_\infty(t)C_h(t-b)dt,
\quad
 W_{S,b}(h)=\frac1H\sum_{q\in\mathcal P}\sum_{j\ge1}
        (\log q)q^{-j/2}C_h(j\log q-b).
\]
The sums are finite after the support test. Under the central-gap condition,
\[
 L_S(v_\theta)=A_0-(J_b+W_{S,b})\cos\theta,
\]
\[
 n_S(v_\theta)=n_{0,S}+\nu_{S,b}\cos\theta,
\quad
 \boxed{e_S(v_\theta)=n_{0,S}-A_0+
              (\nu_{S,b}+J_b+W_{S,b})\cos\theta.}           \tag{24}
\]
**Proof.** Expand the autocorrelation. The central term is \(C_h(t)/H\); the two translated cross terms are
\(\cos\theta[C_h(t-b)+C_h(t+b)]/(2H)\).
The central term vanishes at every prime-power shift, and the \(t+b\) term vanishes for \(t>0\). Substitution into \(\mathcal D\) and the prime sum gives the first line. Expansion of the same Hilbert--Schmidt square gives the second. QED. [ABSTRACT][PAPER]

For general complex \(h\), retain the Hermitian two-by-two form and its sine term. Equivalently use the exact multiplier
\(|\widehat v_\theta|^2=H^{-1}(1+\cos(b\xi+\theta))|\widehat h|^2\) with the stated translation convention. A real-even cosine law is not silently applied to every complex input.

If only \(p\) is active, \(W_{S,b}=w_p=b/\sqrt p\). If prime power 4 is also active in the \(p=5\) window, its extra contribution is
\((\log2)/(2H)\,C_h(\log(4/5))\). Cross terms between different primes also appear in the **projector** through \(B_S^*B_S\); they are not additional prime-pair atoms in the linear arithmetic trace. Differentiating the product phase in (2) remains additive.

### 4.3 An explicit high-modulation family

Choose any real even nonzero \(\eta\in C_c^\infty(-\delta,\delta)\). For \(T>0\), put
\[
 h_T=(\partial_x^2-1/4)(\eta(x)\cos(Tx)).                   \tag{25}
\]
Both pole moments vanish exactly by integration by parts. The function is nonzero: the operator \(\partial^2-1/4\) is injective on compactly supported smooth functions. These are real-even members of the original class, not a replacement by a Fourier-gap class.

After division by \(H_T=\|h_T\|^2\), their Fourier energy escapes every fixed compact and concentrates around \(+T\) and \(-T\) with the fixed envelope supplied by \(\eta\). This follows directly from
\(\widehat h_T(\xi)=-(\xi^2+1/4)(\widehat\eta(\xi-T)+\widehat\eta(\xi+T))/2\), the Schwartz bounds, and \(H_T\sim T^4\|\eta\|^2/2\).

For each **fixed** \(S\), (15) or (18) and boundedness of \(d_S\) therefore imply that every normalized integral of \(d_S\) against this energy, with a bounded phase weight, tends to zero. The archimedean mixed term \(J_b(h_T)\) tends to zero as well: its translated kernel is smooth away from zero, or one may use its absolutely convergent Laplace-moment series and the rapid Fourier decay of \(\eta\).

When only the atom at \(p\) is active, exact phase averaging of the arithmetic symbol gives
\[
 \boxed{
 \nu_{S,\log p}(h_T)\longrightarrow-w_p,
 \quad n_{0,S}-A_0\longrightarrow0,
 \quad e_S(v_{\theta,T})\longrightarrow0.}                  \tag{26}
\]
The convergence is uniform in \(\theta\), for the fixed data. In particular
\(n_S(v_{-,T})-n_\infty(v_{-,T})\to w_p\).
To verify the coefficient, the \(q_\infty\) mixed integral is \(-J_b\); the matching first Euler harmonic contributes \(-w_p\); every other Euler harmonic has zero correlation under the stated gaps; the \(d_S\) integral vanishes. No zeros of zeta and no prime-pair conjecture enter. [ABSTRACT][PAPER]

### 4.4 Exact counterexample to the proposed uniform scaling

The statement \(|\nu_{S,\log p}(h)|\le C p^{-1/2}\), with one constant \(C\) for all primes and all admissible inputs, is false. For each prime choose a positive \(\delta_p\) small enough to isolate its prime-power shift, and a bump \(\eta_p\) as in (25). This is an explicit family; the width is declared, not held fixed while neighboring prime powers enter unnoticed.

Given \(C>0\), choose a prime with \(\log p>2C\). By (26), for all sufficiently large \(T\),
\[
 \boxed{C r_p+\nu_{S,\log p}(h_{p,T})
       <C r_p-\tfrac12(\log p)r_p<0.}                     \tag{27}
\]
This is a strict negative upper bound for the proposed lower constraint \(\nu\ge-Cr_p\), and hence an exact counterexample to the absolute-value bound. The same counterexample already works with the literal one-prime source. A constant allowed to grow like \(\log p\) avoids the contradiction but removes the claimed logarithmic advantage.

**KILL_SCOPE: THEOREM_SHAPE.** The evidence is (25)--(27), not a failed sufficient certificate. Neither the phase inequality for each prime nor the larger RH route is refuted. The limit is taken first in \(T\) for each fixed \(p,S\); no uniform two-parameter estimate is inferred.

For \(p=3,5,7\) the answer is therefore concrete: the matching leading reservoir cross term is \(-\log p/\sqrt p\), not an independently bounded coefficient times \(p^{-1/2}\). The term that contains the supposedly missing growth is the phase derivative \(a_pr_p\), already present in (3). The residual capable of deciding the sign is \(d_S\), with its full finite-prime projector and inverse, not the bare Euler coefficient.

## 5. Q3(a): a sharp uncertainty statement and the zero-lattice obstruction

### 5.1 Exact mass in the periodic dips

For \(0\le\beta\le\pi\), define the actual mathematical set
\[
 \mathcal D_\beta=\{\xi:\operatorname{dist}(a\xi,2\pi\mathbb Z)\le\beta\}.
\]
Lemma 5 gives, for **every** nonzero short-support base test,
\[
 \boxed{
 \frac{\int_{\mathcal D_\beta}(1-\cos(a\xi))|\widehat h|^2d\xi}
      {\int(1-\cos(a\xi))|\widehat h|^2d\xi}
       =\frac{\beta-\sin\beta}{\pi}.}                     \tag{28}
\]
This is an equality, stronger than a generic uncertainty upper bound. For bands of full frequency width \(W\), put \(\beta=aW/2\). Since \(\beta-\sin\beta\le\beta^3/6\), the fraction is at most \(a^3W^3/(48\pi)\). The frozen \(\delta_0\) satisfies the only support hypothesis, \(2\delta_0<a\). Pole-nullness cannot weaken this bound. [ABSTRACT][PAPER]

The positive bands of the **leading** multiplier \(q_\infty/(2\pi)-k_p\) are exactly \(\cos\theta>r_p\). Their half-width is \(\beta_p=\arccos r_p\). For \(p=2\), the minus-phase fraction there is exactly
\[
 \frac14-\frac1{\pi\sqrt2}.                               \tag{29}
\]
For the high-modulation family (25), the fraction lying in the positive set of the **full source** multiplier tends to (29): away from the two phase boundaries the sign agrees eventually by (15), boundary strips have arbitrarily small mass by (20), and the energy in a fixed low-frequency interval vanishes.

Do not replace that assertion by a theorem that every finite-frequency positive component of the true source is contained in the diagnostic width-2-to-3 bands. Such coverage has not been certified. Formula (28) is unconditional for the explicitly defined periodic set; an upper bound for the whole true positive set needs either a proved containment or the residual envelope (7). This distinction is retained in prediction scoring.

There is also a useful exact representation of the remaining freedom. For \(\xi_k=(\theta+2\pi k)/a\), set
\(\rho_h(k\mid\theta)=|\widehat h(\xi_k)|^2/(aH)\). Then \(\sum_k\rho_h(k\mid\theta)=1\), and
\[
 \int W_h f(\xi)d\xi
 =\int_0^{2\pi}(1-\cos\theta)
                  \sum_k\rho_h(k\mid\theta)f(\xi_k)d\theta.
\]
Shaping can change the conditional distribution along a phase fiber, and therefore can affect the nonperiodic correction \(d_S\). It cannot change the phase marginal. This identifies precisely what the no-go does and does not exclude.

### 5.2 Zeros at every odd lattice point are not finite codimension

Suppose \(\widehat h((2k+1)\pi/a)=0\) for every integer \(k\), while \(h\) is supported in an interval of length less than \(a\). Extend \(h(x)e^{-i\pi x/a}\) by zero to an interval of length \(a\). The asserted values are all of its Fourier-series coefficients. Completeness of the Fourier basis implies \(h=0\). [ABSTRACT][PAPER]

Thus the proposed **infinite** lattice of zeros cannot be imposed on a nonzero member of the short class. Any fixed finite list is a legitimate finite-codimension condition and leaves an infinite-dimensional smooth pole-null subspace, but it does not alter (28). It can suppress selected samples or alter a nonperiodic residual; no gain in total periodic-band mass follows. This refutes only the all-lattice construction, not finite interpolation.

## 6. Q3(b): exact lobe arithmetic and an explicit successful notch

Let \(P(z)=\sum_{j=0}^m c_jz^j\), \(s_c=\sum|c_j|^2>0\), and
\[
 v_{P,h}=\frac{\sum_{j=0}^m c_jU_{ja}h}{\sqrt{Hs_c}},\qquad
 A_\ell(c)=\sum_{j=0}^{m-\ell}\overline{c_j}c_{j+\ell}.
\]
Assume disjoint lobes and retain the support gaps needed to exclude other prime-power shifts. Then \(\|v_{P,h}\|=1\),
\(C_{v_{P,h}}(\ell a)=\Re A_\ell/s_c\), and for \(a=\log p\) the arithmetic contribution is exactly
\[
 \boxed{\mathcal A_p(P)=-\frac{2a}{s_c}
                   \sum_{\ell=1}^m r_p^\ell\Re A_\ell(c).} \tag{30}
\]
For arbitrary lobe positions \(x_j\), rather than a prime lattice, use the full formula
\[
 C_v(t)=\frac1{Hs_c}\Re\sum_{j,k}\overline{c_j}c_k
                r_h(t+x_j-x_k),\qquad
 r_h(t)=\int\overline{h(x)}h(x+t)dx,
\]
and insert it into \(-2\sum_n\Lambda(n)n^{-1/2}C_v(\log n)\). This includes atoms near every difference, with the actual overlap and the von Mangoldt weight. There is no weight \(\log n\) at a non-prime-power integer. [ABSTRACT][PAPER]

For the three lobes \(0,a,2a\), \(a=\log2\), require
\(2\delta<\log(5/4)\). Then the prime 3 is inside the outer support window but outside every autocorrelation lobe; it contributes zero. The powers 2 and 4 are both active. One may still retain \(S=\{\infty,2,3\}\) for the full-window source, but its Sonin projection differs from the one-prime source.

**Theorem 6 (a genuine three-lobe notch). [ABSTRACT][PAPER]** Choose
\[
 \boxed{P(z)=2+z-z^2.}
\]
Then \(P(-1)=0\), all three lobes are nonzero, \(s_c=6\), \(A_1=1\), \(A_2=-2\), and
\[
 \boxed{\mathcal A_2(P)=\frac{\log2}{3}(1-1/\sqrt2)>0.}    \tag{31}
\]
**Proof.** Substitute these coefficients into (30), with \(r^2=1/2\). QED.

Its phase weight is \(|P(e^{i\theta})|^2=6+2\cos\theta-4\cos2\theta\), so it moves the exact periodic-band fraction to
\[
 \frac{\beta}{\pi}+
                 \frac{\sin\beta-\sin2\beta}{3\pi}.        \tag{32}
\]
This has a linear small-\(\beta\) term, unlike (28). The gain is purchased with the smaller arithmetic budget (31), not obtained freely by modifying \(h\).

There is an exact optimal atom bound for degree at most two under the notch. Write
\((c_0,c_1,c_2)=(u,u+v,v)\), which is equivalent to \(P(-1)=0\), and put \(s=u+v\), \(d=u-v\). Direct calculation gives
\[
 \mathcal A_p(P)=a\,
 \frac{r^2|d|^2-(4r+r^2)|s|^2}{3|s|^2+|d|^2}
       \le ar^2.                                         \tag{33}
\]
Equality occurs for \(s=0\), namely \(P\) proportional to \(1-z^2\), when the middle lobe vanishes. For \(p=2\) this maximum is \(a/2\), strictly below the original minus-pair atom \(a/\sqrt2\). Formula (33) applies only when the indicated powers are the active atoms; it does not discard other-prime overlaps in a larger general window.

### Does the notch make both sides favourable?

Not automatically. Exact phase averaging gives
\[
 \frac1{Hs_c}\int |P(e^{-ia\xi})|^2|\widehat h(\xi)|^2g_p(a\xi)d\xi
       =\mathcal A_p(P).                                 \tag{34}
\]
Thus the leading periodic reservoir penalty is exactly the positive atom combination, for every polynomial, not only for the minus pair.

Define
\[
 E_S(P,h)=\frac1{Hs_c}\int |P(e^{-ia\xi})|^2|\widehat h(\xi)|^2d_S(\xi)d\xi.
\]
When the displayed arithmetic atoms are the active ones, the **net reservoir part** in the request's split is
\(\mathcal R(P,h)=-\mathcal A_p(P)-E_S(P,h)\), and the full margin is \(-E_S(P,h)\). Hence a positive atom and a nonnegative net reservoir require the precise additional inequality
\[
 \boxed{E_S(P,h)\le-\mathcal A_p(P)<0.}                    \tag{35}
\]
If instead “favourable reservoir” means \(n_S-n_\infty\le0\), replace \(d_S\) in (35) by \(d_S-d_\infty\). These are distinct comparisons, and neither is proved for the notch example.

For (25), \(E_S(P,h_T)\to0\); consequently \(\mathcal R(P,h_T)\to-\mathcal A_p(P)\). A polynomial with a positive atom therefore cannot make both parts favourable throughout this high-frequency family. At finite frequency, existence of a test satisfying (35) remains an explicit residual problem. The successful notch is a real algebraic construction, not a completed Sonin sign theorem.

## 7. Strongest attack and the false-factor discriminator

The strongest objection to turning these results into a positivity proof is that all the attractive leading terms cancel. An \(o(1)\) correction may approach zero from either side. Neither (15), (26), nor the exact phase constraint supplies the sign in (R-SIGN).

This cancellation also gives a new rigorous resolution of the parent's specified false-factor plant. Keep the same Sonin projection and insert
\(M_2(s)=(1-2^{3/4-s})(1-2^{-1/4+s})\) only on the arithmetic side, exactly as in [PP]. Its known lattice contribution on the normalized minus class is
\(-\delta_M\), where
\(\delta_M=2a(\cosh(a/4)-1)>0\). Thus
\[
 \mathfrak m_\sharp(h_T)=\mathfrak m(h_T)-\delta_M.
\]
By (21), (25), and (15), \(\mathfrak m(h_T)\to0\), so
\[
 \boxed{\mathfrak m_\sharp(h_T)<-\delta_M/2<0
                    \quad\text{for all sufficiently large }T.} \tag{36}
\]
This is a strict negative upper envelope on an explicit infinite family in the original pole-null class. **Whole-class survival under this particular plant is refuted.** Survival of the observer's one finite-margin row is compatible with (36). The genuine-source inequality (R-SIGN) is not refuted, and no native Sonin model for the artificial local factor is asserted. [ABSTRACT][PAPER]

The argument gives a useful **DISCRIMINATOR for zero-consistent margins**: test the signed angle functional \(E_S(P,h)\), and compare the planted margin with \(-\delta_M\), rather than declare a small original margin to be exact zero. For the original source, a certified upper bound \(U(\mathfrak m)<0\) is a counterexample; a lower bound \(L(\mathfrak m)\ge0\) is a finite-test certificate. A zero-straddling enclosure is neither.

## 8. Predictions, next bounded task, and closeout

### 8.1 Frozen observer predictions

The probabilities are not edited. A paper determination below is not an independent Lean or interval verification.

| Prediction | Frozen p | Fate in this adjudication |
|---|---:|---|
| P_AMPLITUDE_NONDECREASING | 0.50 | CONFIRMED for its stated nondecay event: every fixed Euler harmonic persists by (16). Literal monotonicity of a fitted envelope was not proved and is not substituted for this event. |
| P_RESONANCE_ALWAYS_ADVERSE | 0.60 | UNRESOLVED on the whole class. Equation (R-INC) is the exact remainder; (26) proves adversity on the high-modulation tail only. |
| P_PRIME_SCALING_RP | 0.55 | REFUTED as the compound uniform-scaling/logarithmic-win claim. The source matching cross term tends to \(-a_pr_p\); (27) refutes a prime-uniform bounded-times-\(r_p\) estimate. |
| P_UNCERTAINTY_NOGO | 0.65 | PARTIAL: the stronger equality (28) proves the periodic-dip no-go. Literal coverage of every positive band of the full finite-frequency source by those dips remains unverified; that broader event is not scored as fully confirmed. |
| P_LOBE_POLYNOMIAL_HELPS | 0.30 | CONFIRMED as written: (31) gives a notch and a favourable atom. A favourable full reservoir was not part of that proven implication. |

The request's diagnostic cosine-law agreement is retained as diagnostic agreement. No carrier value is used in the proofs or silently promoted to an enclosure.

### 8.2 Judge registration and its fate

The following analytical candidates were registered in local scratch before their paper adversarial closeout, after reading the request and the pinned definitions. They are not blind predictions preceding the supplied diagnostics. No numerical or symbolic-software test was performed.

| Judge prediction | p | Fate |
|---|---:|---|
| P_R_PERIODIZATION_SURVIVES | 0.99 | Derived in (20), with the all-lattice falsifier; independent review pending. |
| P_R_SOURCE_REMAINDER_DECAYS | 0.76 | Paper derivation (5)--(18) supplied, including generalized-wave and trace-domain checks; independent review pending. |
| P_R_PEAK_NOTCH_AND_POSITIVE_ATOM | 0.97 | Exact construction (31) and constrained optimum (33) supplied; independent review pending. |
| P_R_LOG_GAIN_FAILS | 0.94 | Exact high-modulation counterexample (27) supplied; independent review pending. |

Do not count self-verification as an independent confirmation of “survives review.” A failure in the source Mellin/trace identification reopens (15)--(18), (26)--(27), and (36); it does not affect the elementary phase theorem (20), the zero-lattice obstruction, or the polynomial arithmetic (30)--(33).

### 8.3 Cheapest decisive check and two representations

The cheapest first check is already analytic: verify the phase-marginal identity and the sign of the Euler phase derivative. This rules out the proposed arbitrary phase-band redistribution and exposes the missing \(\log p\) without a larger carrier.

For an independent source check, use (6) and (10), not a fit to \(k_2-q_\infty/(2\pi)\). The first complete-period cosine coefficient
\[
 \mathcal C_1(X)=\frac a\pi\int_X^{X+2\pi/a}
                      (k_p-k_\infty)(\xi)\cos(a\xi)d\xi
\]
has the registered target \(-ar/\pi+O_p(X^{-1/2})\). The corresponding sine coefficient tends to zero. A carrier comparison must include both the source error and the Fourier quadrature error before disagreement diagnoses the theorem. Fixed \(N\) at indefinitely increasing \(X\) is expressly not this test.

Two concrete representations remain available, with ordinal estimates rather than measured runtimes:

| Representation | Object retained | Kill-power / cost estimate | Risk |
|---|---|---|---|
| Source Mellin/finite-interval resolvent, (6), (10)--(14) | \(u_S,t_S,(I-A_S^2)^{-1}\), with all norm and scalar tails | 9/10 power, 4/10 cost for a fixed-prime independent identity check | singular Mellin-wave regularization or an omitted quadrature/operator error |
| Exact phase marginal plus signed residual test-space compression, (20)--(23), (35) | original support and pole-null class; Hermitian polarization of \(E_S\) | 8/10 power, 5/10 cost for a small packet; higher for a whole-class complement | diagonal-only testing or loss of the infinite test-space complement |

No escalated computation is authorized in this adjudication.

### 8.4 One CODEX DIRECTIVE — paper audit only

**Target:** independently audit the single source statement
\[
 k_{\{\infty,2\}}(\xi)-\frac{q_{\{\infty,2\}}(\xi)}{2\pi}
       =d_2(\xi)\text{ of (6)},\qquad d_2(\xi)=O(|\xi|^{-1/2}).
\]
**Inputs:** the pinned [PP] definitions; [CCM23] finite Euler multiplier; equations (1)--(18) of this verdict.

**Required checks:** rederive the block inverse (9), the gamma/reflection sign (2)--(3), the factor \(1/\pi\) and the opposite frequency in \(t_p\), the tested trace-class passage, and both regimes in (11)--(12). Test the unprimed case and the \(P(-1)=0\) arithmetic independently. Preserve all cutoffs and the nonunitary transform convention. Do not replace \(G^{-1}\) by an uncompressed inverse or \(A_S\) by a polar-adjusted carrier.

**Success:** an independent paper check establishes the same source identity and decay, with no additional unproved domain assumption. **Failure:** return `RESONANCE_MELLIN_DENSITY_IDENTIFICATION_GAP` or `RESONANCE_OSCILLATORY_TAIL_BOUND_GAP`, naming the first exact failing equality/estimate and the weakest repair. A missing implementation is `RESEARCH_DEBT`, not mathematical refutation.

**Execution boundary:** no Lean edit, no new numerical run, no queue binding, no Aristotle, no state promotion. No `lake` gate is applicable to this document-only paper audit. A later numerical transaction requires its own declared finite packet and error supplier.

### 8.5 Consumer-first dependency record

**DOWNSTREAM_CONSUMER:** the unchanged all-complex compact-smooth Weil criterion.

**ACTUAL_CONSUMER_REQUIREMENT:** nonnegativity of the actual Weil form on that full class. The fixed minus-lobe minorant is an intermediate restricted-class target, not a necessary equivalent formulation of that consumer.

**ORIGINAL_REQUESTED_OBJECT:** reservoir amplitude law, prime-scaling advantage, and a shape/no-go mechanism sufficient to settle the restricted sign.

**ORIGINAL_OBJECT_IS:** `NOT_NECESSARY` for the global consumer; the restricted inequality itself is not established as necessary. A logarithmic advantage is also not necessary for (R-SIGN).

**KNOWN_WEAKER_INTERFACES:** direct proof of (R-SIGN); a signed kernel comparison on the exact pole-null class; or a finite packet bound plus a proved full complement/coupling bound. Each reaches the restricted sign only with its stated quantifiers. Extension to the global consumer still needs an exhausting all-test bridge, not just more separated-lobe examples.

**FAILURE_TYPE:** `NO_DERIVATION` for the universal residual signs; `COUNTEREXAMPLE` for the precise uniform \(Cr_p\) claim and the whole-class false-factor survival; `INCOMPATIBILITY` for imposing all odd-lattice zeros on a nonzero short-support function.

**EPISTEMIC_STATUS:** universal residual signs are `RESEARCH_DEBT`; the three exact theorem shapes listed in the header are `MATHEMATICALLY_DEAD` only at their declared scope. No `ROUTE_FAMILY` death is claimed.

**NOVELTY_AXIS:** preserve the entire finite-Euler phase and the compact-support phase marginal before estimating the nonperiodic angle correction. Historical priority is not claimed.

**REOPEN_TRIGGER:** for the sign debt, a certified source counterexample or a proof of (R-SIGN)/(R-INC) with the exact complement; for simultaneous favourable notch terms, a proof or certified witness for (35); for multiplets, an error-controlled comparison to (6). The global-class bridge remains separately open even after a restricted-class success.

### 8.6 Verification handoff and memory

Only `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_RESERVOIR_RESONANCE_AND_PRIME_SCALING_2026-09-06.md` is written, on `rh_clean`. The exact commit SHA and blob are returned in the publication receipt after the write and readback; they cannot be embedded self-referentially in the immutable file that creates them. No Lean file is written. Therefore no Lean blob, axiom profile or compilation result is claimed. All new mathematics has verifier **PAPER**, pending independent checking.

The readback gate checks the request ID, operative class, exact expected path and the one-file commit. That gate changes publication status only. It does not upgrade any paper proof to `LEAN`, any diagnostic to `ARB_INTERVAL`, or either residual sign to proved.

```yaml
META_CLOSEOUT:
  PROGRESS_CLASS: PROOF_PROGRESS
  COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
  ROUTE_SCORE: 5
  WHAT_BECAME_SMALLER:
    - amplitude_question_reduced_to_explicit_periodic_symbol_plus_decaying_angle_density
    - shaping_freedom_reduced_to_conditional_weights_inside_phase_fibers
    - phase_sign_is_exactly_the_signed_angle_functional_not_atom_minus_unrelated_reservoir
  WHAT_WAS_REFUTED:
    - prime_uniform_C_times_rp_bound_and_its_logarithmic_win_inference
    - nonzero_short_test_with_all_odd_lattice_Fourier_zeros
    - whole_class_survival_of_the_specified_false_local_factor
  MUST_NOT_RECUR:
    - infer_source_asymptotics_by_sending_frequency_to_infinity_at_fixed_carrier
    - call_all_odd_lattice_constraints_finite_codimension
    - replace_autocorrelation_support_by_its_outer_interval
    - treat_a_peak_notch_as_a_signed_reservoir_certificate
    - infer_a_sign_from_an_o_1_remainder
    - omit_the_log_p_from_the_Euler_phase_derivative
  SMALLEST_SIGN_GAP: R_SIGN_on_the_exact_pole_null_short_minus_class
  NEXT_CHEAPEST_DECISIVE_TEST: independent_paper_audit_of_equations_6_and_10_through_18
  MEMORY:
    target: REQ-2026-09-06-RESONANCE
    status: PROGRESS
    invariant_learned: arithmetic_atom_and_periodic_Sonin_increment_have_the_same_log_p_scale
    forbidden_future_move: claim_logarithmic_dominance_from_the_bare_Euler_coefficient
    remaining_unknown: sign_of_the_nonperiodic_angle_density_after_exact_class_testing
```
