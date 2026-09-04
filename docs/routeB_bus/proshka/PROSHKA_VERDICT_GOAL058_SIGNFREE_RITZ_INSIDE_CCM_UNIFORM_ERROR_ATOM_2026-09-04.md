# STATUS: KILL_PMINUS_AS_STRICTLY_WEAKER_THAN_RH
```yaml
OPERATIVE_CLASS: KILL_PMINUS_AS_STRICTLY_WEAKER_THAN_RH
PRIMARY: STILL_RH_EQUIVALENT
PRIMARY_COUNT: 1
ANSWER: B
REQUEST_ID: REQ-2026-09-04-SIGNFREE
BOUNDARY_ID: GOAL058_SIGNFREE_RITZ_INSIDE_CCM_UNIFORM_ERROR_ATOM

REQUEST_LOCK:
  COMMIT: f7f6b91cdec7f8362a858f7a7974f685d24e78db
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_SIGNFREE_RITZ_INSIDE_UNIFORM_ERROR_2026-09-04.txt
  GIT_BLOB: 416596d51d30d8511ee9afe732e54a891af98fd9
  SHA256: a7e2c3f27e709870ba805f523df40e99a7a1c3e18c0ac0efb534318f67e9e4d1
  BYTES: 11666
  LINES: 117
  FINAL_LF: true
  HASH_VERIFIED: true
  METHOD: fetched_UTF8_reencoded_and_independently_hashed_with_hashlib
  GIT_OBJECT_SHA1_RECOMPUTED: true
  SHA256_RECOMPUTED: true

PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_G1_G3_COFINAL_GROUND_TRACKING
  SOURCE_OBJECT_FAMILY_ID: PROPOSITION59_CCM_FINITE_BOTTOM_GROUND_FAMILY
  TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false

EVIDENCE_BOUNDARY:
  REPOSITORY_CUTOFF: f7f6b91cdec7f8362a858f7a7974f685d24e78db
  SHELF_BASE: 0f58282e
  WRITE_BASE_OBSERVED: 0c08d8566803476575fc218b50620bcea754dad6
  WRITE_BASE_USED_AS_MATHEMATICAL_EVIDENCE: false
  POST_REQUEST_REPOSITORY_RESULTS_USED: false
  PRIMARY_PAPER_RESEARCH: performed_for_Q1_Q3
  NEW_DERIVATIONS: explicitly_marked_PAPER_NOT_LEAN
  REVIEW_BOUNDARY: PAPER_ADJUDICATION_ONLY
  AUTHORIZED_WRITE_SCOPE: VERDICT_DOC_ONLY
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SIGNFREE_RITZ_INSIDE_CCM_UNIFORM_ERROR_ATOM_2026-09-04.md

DECISIONS:
  SF_FINITE_INEQUALITY: ACCEPTED_WITHOUT_BOTTOM_SIGN
  SF_RATE_IMPLIES_PROJECTIVE_DECAY: ACCEPTED_WHEN_GAP_POSITIVE
  PROJECTIVE_DECAY_IMPLIES_SF_RATE: FALSE_IN_GENERAL
  PMINUS_ALONE_IMPLIES_SF_RATE: FALSE_WITHOUT_TRIAL_ENERGY_SCALE
  PMINUS_CANONICAL_CCM_WIDE_FAMILY: RH_EQUIVALENT
  RAW_SF_RATE_WITHOUT_TRIAL_ENERGY_HYPOTHESIS: NOT_SHOWN_RH_EQUIVALENT
  COMPACT_CAUCHY_SCHWARZ_INEQUALITY: LEAN_READY
  COMPACT_CONSTANT_POLYNOMIAL_IN_LOG_LENGTH: FALSE_OFF_REAL_AXIS
  PROJECTIVE_DECAY_ALONE_IMPLIES_COMPACT_DECAY: FALSE
  UNIFORM_CENTRAL_COEFFICIENT_FLOOR_FROM_SAMPLING: FALSE
  RELATIVE_RAYLEIGH_UPPER_RATIO_ALONE_IMPLIES_POSITIVE_BOTTOM: FALSE
  CCM_NO_LOWER_BOUND_OF_ANY_KIND: FALSE
  UNCONDITIONAL_TARGET_LOWER_BOUND_FOUND: false

B_SCOPE:
  FULL_CONTINUUM_BOTTOM: proved_on_paper
  LITERAL_FINITE_FULL_CCM_BOTTOM_WITH_N_GE_M: proved_on_paper_via_fixed_test_recovery
  EVEN_ONLY_BOTTOM: requires_the_explicit_even_Weil_criterion_not_even_equals_full
  EVEN_CRITERION_SOURCE: Yoshida_1992_Proposition_1_2_as_reproduced_in_pinned_WEIL_POSITIVITY_OBJECT_CARD_section_1_5
  EVEN_PRIMARY_SCAN_INDEPENDENTLY_RETRIEVED_THIS_RUN: false
  ARITHMETIC_WINDOW_RANGE: m_tends_to_infinity_and_N_m_ge_m
  ARBITRARY_ABSTRACT_PairCofinal_WITHOUT_RECOVERY: not_covered
  NUMERICAL_SATURATION_REQUIRED_FOR_THIS_IMPLICATION: false

KILL_SCOPE: THEOREM_SHAPE
KILL_EVIDENCE_KIND: fixed_test_minmax_upper_bound_plus_negative_witness_persistence
FAILURE_TYPE: INCOMPATIBILITY
EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
KILLED_CLAIM: PMINUS_is_strictly_weaker_than_RH_for_the_literal_exhausting_CCM_family
NOT_KILLED:
  - the_sign_free_Ritz_inequality
  - independent_proof_of_an_RH_sufficient_estimate
  - the_ground_trial_research_route
PINNED_EVIDENCE: request_sections_2_4_and_proofs_Q1_1_through_Q1_4_below

CLOSES:
  - REQ-2026-09-04-SIGNFREE
CLOSES_ANALYTIC_SUPPLIERS: []
OPENS: []
LEAN_EDIT_PERFORMED: false
LEAN_KERNEL_RERUN: false
NUMERICAL_RUN_PERFORMED: false
ARISTOTLE_SUBMISSION: false
ROUTE_PROMOTION: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## 0. Verdict and notation

**Answer B applies to (P-) on the literal CCM continuum family and on every wide finite schedule N(m) >= m, not to an arbitrary sequence of symmetric matrices.** The finite inequality (SF) really is sign-free. The proposed asymptotic lower bound is not sign-free in its global consequence. The sign returns through a uniform **upper bound on the second level**, followed by persistence of one fixed negative test. No exponential gap estimate is needed for that argument. [COFINAL_FAMILY][PAPER]

This does not establish (P-), disprove RH, or prohibit proving an RH-sufficient condition independently. It rejects the classification of (P-) as a strictly weaker substitute. Implication to RH is not circular reasoning; using RH to supply the premise would be circular.

Use L = log m, lambda = sqrt(m), and let b_m <= s_m be the lowest two eigenvalues of the stated operator or compression. Write a_m = R(q_m), Delta_m = s_m - b_m, and

    eta_m = (a_m - b_m) / Delta_m.

This separates the gap Delta_m from the request's curvature difference delta. To make (P-) unambiguous, use its dominated-little-o form:

    there exist e_m >= 0 with e_m -> 0 and
    b_m >= -e_m * |s_m| eventually.                         (Pminus)

When s_m > 0 this is the request's intended statement. It also exposes what happens if the second level is negative or zero. No numerical value of s_m is assumed to satisfy a cofinal law.

**Important correction to the earlier relay:** R/mu <= C alone does not imply mu >= R/C. Multiplication by mu requires its sign. For R = 1, mu = -1 and C = 2 the ratio condition holds and the claimed lower bound fails. The valid positive-floor statement is mu >= R/C > 0, or a ratio condition with positivity of the denominator independently included. Neither the request nor this verdict may conceal that sign. [ABSTRACT][PAPER]

## Q1. The hidden sign: a proof, not another saturation conjecture

### Q1.1 Continuum: the second eigenvalue cannot escape to positive infinity

Let nu_1(lambda) = mu_lambda and nu_2(lambda) be the first two levels of the full semilocal Weil operator. Fix two linearly independent smooth functions in one fixed window, and let V be their two-dimensional span. For every larger window, V is still admissible and its Weil form and L2 norm are unchanged. Therefore min-max gives

    nu_2(lambda) <= max_{0 != f in V} QW(f,f)/||f||_2^2 <= M,

for one finite M > 0, independent of the enlarged window. This is an **upper** bound; precisely the direction that was useless for a gap lower bound is decisive here. It uses only a fixed finite-dimensional test space and the source form, not a trial-ground approximation. [COFINAL_FAMILY][PAPER, DERIVED]

If Pminus holds and e_m < 1, then s_m < 0 is impossible: ordering gives b_m <= s_m = -|s_m| < -e_m|s_m|. If s_m = 0, Pminus and ordering give b_m = 0. Thus eventually s_m >= 0 and

    b_m >= -e_m M,              liminf b_m >= 0.

Apply this to b_m = mu_{sqrt(m)}. For any fixed lambda_0 > 1, choose arbitrarily large m with sqrt(m) > lambda_0. CCM (3.27) gives

    mu_{lambda_0} >= mu_{sqrt(m)} >= -e_m M.

Let m tend to infinity: mu_{lambda_0} >= 0. Every fixed window is nonnegative. The localized Weil criterion then gives RH. This argument does **not** require R(q_lambda) -> 0 or Corollary 3.8's more specific zero-limit hypothesis. [COFINAL_FAMILY][PAPER, DERIVED FROM CCM 3.27 AND WEIL]

Conversely, RH gives nonnegativity on all test functions and hence on all such compressions, so Pminus holds with e_m = 0. This is the claimed equivalence for Pminus; it is not an equivalence asserted for eta_m -> 0 with an arbitrary trial.

**Falsifier for omitting the second-level bound:** diag(-1,m) has a constant, hence nonincreasing, negative bottom and b_m/|s_m| -> 0. It is not a nested CCM spectral family: its second level escapes to infinity. Thus monotonicity of the bottom alone is not the complete proof. [ABSTRACT][PAPER]

### Q1.2 Finite diagonal: fixed-window convergence cannot simply be substituted

CCM Proposition 3.4 gives the limit as N -> infinity for each fixed m. It does not by itself give a joint diagonal convergence rate. Also, b_{m,N} >= mu_{sqrt(m)}, not the reverse. We do not replace either fact by observed saturation.

For the authorized wide schedules N(m) >= m, a much weaker recovery statement suffices: every **fixed smooth test**, and every fixed two-dimensional smooth test space, is approximated in the Weil form along that diagonal. Here is a direct proof using the geometric-side form. [COFINAL_FAMILY][PAPER, NEW DERIVATION]

Work in logarithmic coordinates on J_L = [-L/2,L/2]. Take f in C_c^infinity(R), supported in a fixed smaller interval. Let P_{L,N} be the orthogonal Fourier projection onto modes |n| <= N on J_L, extended by zero outside J_L. Its Fourier coefficients are

    c_n = L^(-1/2) integral f(t) exp(-2*pi*i*n*t/L) dt.

Four integrations by parts, with no boundary terms for the fixed test, give for j = 0,1

    ||partial^j(P_{L,N}f-f)||_{infinity,J_L}
       <= C_f (L/N)^(3-j).

For N >= m and m large, both are bounded by

    eps_{m,N} = C_f (L/N)^2.

The zero-extended error h = P_{L,N}f-f has L1 norm at most L eps and total variation at most (L+2) eps; this explicitly includes its two endpoint jumps. Thus

    |hat h(t)| <= (L+2) eps * min(1,1/|t|)

with an inessential absolute enlargement near t = 0. The archimedean multiplier is bounded in absolute value by C log(2+|t|); its error energy is consequently at most C(L+2)^2 eps^2, and its mixed term with the fixed f tends to zero.

The pole functionals obey |hat h(+-i/2)| <= L m^(1/4) eps. The prime part is a sum of truncated translations with operator norm bounded by

    2 sum_{2 <= n <= m} Lambda(n)/sqrt(n) <= C sqrt(m) log m.

Cauchy-Schwarz bounds its mixed error by this norm times
2||f||_2||h||_2 + ||h||_2^2. Combining the three contributions yields, for large m and N >= m,

    |QW(P_{L,N}f,P_{L,N}f) - QW(f,f)|
       <= C_f sqrt(m)(1+L)^2 (L/N)^2
       <= C_f sqrt(m)(1+L)^2 L^2/m^2 -> 0.              (REC)

Here C_f is independent of m and N. The form identity used is Connes-Consani, 2106.01715, Proposition 2.1, equivalently CCM (3.7)-(3.11); these sources supply the decomposition, while the joint estimate (REC) is the derivation above. It is not attributed to CCM as a previously printed diagonal theorem. No zero-side positivity enters the estimate. The error bound pays a crude growing prime bound, which a fixed smooth test's Fourier tail easily beats.

The same argument is uniform on the unit sphere of any fixed finite-dimensional smooth space. Its Gram matrix converges to the original Gram matrix. Consequently there is M > 0 such that s_{m,N(m)} <= M eventually. This proves the finite counterpart of Q1.1 without resolving the extraordinarily small true ground scale.

If RH were false, the full Weil criterion supplies a fixed normalized smooth f with QW(f,f) < 0. By (REC), for some c > 0,

    b_{m,N(m)} <= R(P_{L,N(m)}f) <= -c

for every sufficiently large m. This contradicts the lower bound -e_m M from Pminus. Equivalently, Pminus makes every fixed smooth test nonnegative, and hence forces mu_lambda >= 0 on every window. [COFINAL_FAMILY][PAPER]

**This is the exact finite-to-global bridge used here.** It recovers fixed tests at coarse accuracy. It neither supplies nor assumes a relative saturation estimate b_{m,N} <= 2 mu_{sqrt(m)}. An expensive tiny-eigenvalue saturation law is unnecessary for this particular implication.

### Q1.3 Sector and schedule boundaries

The request's numerical rows use the even block; the full operator's bottom is not automatically the even bottom. For an even-block formulation, apply (REC) to even tests and the same fixed-two-test min-max argument within that sector. The final implication then uses the **even-test Weil criterion**, not an assertion that the even and full minima coincide.

The pinned `WEIL_POSITIVITY_OBJECT_CARD_2026-09-04.md`, section 1.5, reproduces Yoshida (1992), Proposition 1(2), p.285: even positivity detects all nonreal exceptions to RH. For the Riemann zeta function the real interval 0 < s < 1 contains no zeros: the alternating Dirichlet series is positive there and 1-2^(1-s) is negative. Thus the even-test criterion also gives RH. This is an explicit PAPER import from the recorded primary-source excerpt; the Yoshida scan was not independently rendered in this session. The full-space proof above does not depend on this parity import. [COFINAL_FAMILY][PAPER]

The schedule assertion is **for every N(m) >= m**, including the frozen N = 8m. Bare `PairCofinal` imposes only two separate divergences; on its own it does not imply (REC). A much slower path needs its own test-recovery proof. Do not silently expand the B verdict to every abstract inhabitant of the roof record. Conversely, every schedule actually under consideration in this wide-schedule request satisfies the explicit recovery estimate above. [COFINAL_FAMILY][PAPER]

### Q1.4 The negative-part dichotomy

Under not-RH, the fixed negative witness persists with an absolute margin c > 0. Meanwhile the second level is bounded above by M. Whenever s_m > 0,

    (-b_m)/s_m >= c/M > 0.

If s_m <= 0, Pminus already fails eventually by ordering, except the impossible case b_m = s_m = 0 in the presence of the negative witness. Therefore the negative part cannot be o(s_m) on the genuine exhausting family. The constant c/M need not be effective without an explicit negative witness, and it is not a numerically fitted constant. [COFINAL_FAMILY][PAPER]

This answers Q3(b) at the same time. It does not establish a universal exponential law for the negative bottom and does not say that RH is false.

## Q2. Typed chain: what survives, what fails

### S1 — sign-free spectral inequality

**Statement.** For every finite real symmetric K, an orthonormal ordered eigenbasis u_j, and ||q||_2 = 1, put w_j = |<q,u_j>|^2. Then

    (lambda_2-lambda_1)(1-w_1)
      <= sum_j (lambda_j-lambda_1)w_j
      = R(q)-lambda_1.                                  (SF)

**Type:** LEAN-READY finite spectral algebra; no sign of lambda_1 or lambda_2 is required. Inputs are the spectral decomposition, w_j >= 0, and sum w_j = 1. A positive Delta is required only to divide. A multiple bottom needs the whole bottom spectral projector and the first level above that cluster instead of an arbitrary chosen u_1. [FINITE_CELL][PAPER]

**K3:** retains the exact matrix, eigenvalue order, unit norm and projector. Drops no sign because none was used. **FIRST_FAILURE:** division at Delta = 0 or replacing the whole bottom by a second-even level without a sector lock.

**Plant:** diag(-2,-1), q = (sqrt(1-t^2),t), 0 <= t <= 1, gives equality Delta*p = R-lambda_1 = t^2. This is the mandatory negative-bottom positive control.

### S2 — (P-) is not by itself the Ritz-rate premise

**Statement.** Suppose eventually s_m > 0 and a_m/s_m -> 0. Rayleigh's minimum gives b_m <= a_m. Under this extra source-energy scale,

    Pminus  <=>  b_m/s_m -> 0  <=>  eta_m -> 0.

Indeed, with r_m = a_m/s_m and t_m = b_m/s_m,

    eta_m = (r_m-t_m)/(1-t_m),
    t_m = (r_m-eta_m)/(1-eta_m).

These are exact algebraic identities where denominators are nonzero. **Type:** CONDITIONAL on the cofinal source theorem a_m/s_m -> 0; that theorem is not supplied by two small observed ratios. R(q) <= lambda_2 is not a substitute for a/s -> 0. [COFINAL_FAMILY][PAPER]

**FIRST_FAILURE:** the source numerator relative to the second level is not bounded at the required scale. **Plant:** K = diag(0,1), q equal to the second eigenvector. Pminus holds, a/s = 1, and eta = p = 1. Thus the unqualified first arrow of the proposed chain is false.

### S3 — Ritz rate to projective distance is one-way

**Statement.** Delta_m > 0 and eta_m -> 0 imply p_m <= eta_m -> 0. After sign/phase alignment,

    d_m^2 := ||xi_m-q_m||_2^2
       = 2(1-sqrt(1-p_m)) <= 2p_m <= 2eta_m.

**Type:** LEAN-READY scalar/spectral assembly. **FIRST_FAILURE of the converse:** a tiny mass in a high-energy mode can dominate the Rayleigh excess. [COFINAL_FAMILY][PAPER]

**Plant:** K_m = diag(0,1,m^2), q_m = (sqrt(1-m^-2),0,m^-1). Then p_m = m^-2 -> 0 but eta_m = 1. The request's `iff-ish` must be replaced by an implication, unless an additional upper spectral-energy bound is supplied.

### S4 — exact P59 compact norm, with the correct growth

Let T_{L,N}c be the literal raw P59 transform, with the removable values at every lattice pole included. Define

    C_N(K,L) = sup_{z in K} sqrt((1/L) sum_{|n|<=N}|K_{L,n}(z)|^2).

Then ||T_{L,N}c||_K <= C_N(K,L)||c||_2. This is the finite Cauchy-Schwarz statement and is **LEAN-READY**. The source kernel and removable values are fixed by `Proposition59EntireTransform.lean`, blob `6d38df2ff26cc7dc7eadc4757c15605649cbb6d4`, at the request commit. [FINITE_CELL][PAPER]

The integral identity

    K_{L,n}(z) = (-1)^n integral_{-L/2}^{L/2} exp(i(z-2*pi*n/L)t) dt

holds also at its removable point. Bessel's inequality therefore gives, with sigma = sup_{z in K}|Im z|,

    C_N(K,L) <= B_sigma(L),
    B_0(L) = sqrt(L),
    B_sigma(L) = sqrt(sinh(sigma*L)/sigma), sigma > 0.    (KERNEL)

This bound is independent of N. It is exponential in L off the real axis, not polynomial in L. Already the n = 0 entry at z = i sigma gives

    C_N({i sigma},L) >= 2 sinh(sigma*L/2)/(sigma sqrt(L)).

With L = log m, the upper bound has scale m^(sigma/2), not a fixed power of log m. **FIRST_FAILURE:** the request's `C(K,L) = poly(L)` is false on any compact containing a fixed nonreal point. No spectral calculation is needed to refute it. [COFINAL_FAMILY][PAPER]

### S5 — anchor transfer, not anchor creation

For phase-aligned unit rows v,q, assume |q_0| >= b > 0 and d = ||v-q||_2 <= b/2. Then |v_0| >= b/2. By linearity and T(c)(0) = sqrt(L)c_0,

    ||T(v)/T(v)(0) - T(q)/T(q)(0)||_K
      <= [2 C_N(K,L)/(sqrt(L)b)](1+1/b) d.             (ANCHOR)

**Type:** LEAN-READY finite norm algebra conditional on the explicit anchor and distance guards. There is no need to assume an independent ground-anchor floor if a trial-anchor bound and d <= b/2 are supplied. [FINITE_CELL][PAPER]

A useful sharper version, when M_q(K) = ||T(q)/T(q)(0)||_K is already bounded, is

    ||T(v)/T(v)(0) - T(q)/T(q)(0)||_K
      <= [C_N(K,L)+sqrt(L) M_q(K)] d /(sqrt(L)|v_0|).

Neither version produces the source anchor bound. Sampling is an equality, not a lower-bound theorem. A normalized fixed smooth localized function f, projected onto longer windows, has

    q_0 = (integral f)/(sqrt(L)||P_{L,N}f||_2),

which is asymptotic to a nonzero constant divided by sqrt(L), not bounded below by a constant. Window concentration therefore does not justify |q_0| >= c > 0. This example diagnoses the claimed inference; it is not asserted to be an asymptotic theorem for the current Ferrers trial. [COFINAL_FAMILY][PAPER]

### S6 — the remaining rate cannot be erased

**Statement.** On the same schedule, a sufficient kernel-facing condition is

    for every K compactly contained in the strip,
    [2 C_N(K,L_m)/(sqrt(L_m)b_m)](1+1/b_m) sqrt(2eta_m) -> 0,

with |q_{m,0}| >= b_m > 0 and sqrt(2eta_m) <= b_m/2 eventually. Then (ANCHOR) gives the compact consumer. The b_m in this display is an anchor budget, not the eigenvalue notation of Q1. To avoid implementation collisions, an actual source file must call it `anchorBudget_m`. [COFINAL_FAMILY][PAPER]

**Type:** CONDITIONAL rate assembly. The source theorem proving this weighted product is NEW-MATH / RESEARCH_DEBT, not supplied by eta_m -> 0. Alternatively, the sharper version can consume the actual trial's compact bound and raw anchor. No new free rate premise is authorized as a supplier discharge.

**Exact counterexample to rate-free transfer:** let L -> infinity, sigma in (0,1/2), q = e_0, b = (e_1+e_{-1})/sqrt(2), t_L = L exp(-sigma L/2), and v_L = sqrt(1-t_L^2)e_0+t_L b, for sufficiently large L. Both central coefficients stay bounded away from zero and p_L = t_L^2 -> 0. Nevertheless

    T(v_L)(i sigma)/T(v_L)(0) - T(q)(i sigma)/T(q)(0)
       -> sqrt(2)/sigma != 0.

This follows by substituting the two pole kernels. The example refutes the generic transfer inference, not a source-specific Ferrers estimate. If desired, K_L = I-v_L v_L^T makes v_L the simple ground and eta_L = p_L, so even the full sign-free Ritz rate holds in the plant. [COFINAL_FAMILY][PAPER]

The request's statement that p decays super-exponentially on saturated cells is not a cofinal theorem. The exponential scale of the eigenvalues is a different quantity from the rate of their projective overlaps.

### S7 — closing the unchanged consumer

Compact ground-to-finite-trial decay plus finite-trial-to-continuum-trial decay and CCM Lemma 7.3 imply the same anchored ground transforms converge locally uniformly to centeredXi, after the fixed scalar/gauge crosswalk. Real-zero transfer additionally requires the actual simple-even bottom package. **Type:** CONDITIONAL assembly into the existing terminal consumer, not a new proof of its missing premises. [COFINAL_FAMILY][PAPER]

The sign-free finite inequality supplies none of: the relative source-energy rate, the anchor budget, the weighted compact rate, or the cofinal simple-even package. Lemma 7.3 concerns the continuum trial and must not be substituted for the finite-projection crosswalk.

## Q3. Supplier landscape and the right falsifiers

### Q3(a): what lower bounds actually exist

The statement that CCM has no lower bound of any kind is false literally: Proposition 3.3 is lower semiboundedness. Its proof source, Connes-Consani 2106.01715, Proposition 2.1, also gives a coarse explicit form. If a_min is a lower bound for the archimedean multiplier, then

    mu_lambda >= a_min - 2(lambda-lambda^-1)
                         - 2 sum_{2<=n<=lambda^2} Lambda(n)/sqrt(n).

The rank-two pole term has norm at most 2(lambda-lambda^-1), and each translation contribution is bounded by Cauchy-Schwarz. This is an unconditional, generally deteriorating, lower bound. It is not -o(nu_2), nor a lower bound tending to zero. [ABSTRACT][PAPER, DERIVED FROM THE SOURCE FORM]

| Source | What it supplies | Why it does not supply Pminus |
|---|---|---|
| CCM 2511.22755, Props.3.3-3.4, Cor.3.7, section 8 | Semiboundedness, a form core, fixed-window Ritz convergence, bottom monotonicity; the missing approximation step is explicit. | No large-window vanishing-negative lower bound. |
| Yoshida 1992, Prop.1, Thms.1-2, as recorded in the pinned source card | Localized/even Weil criteria, small-window positivity, nondegeneracy criterion. | A small window does not supply the cofinal lower bound. The underlying scan was not independently rendered here. |
| Bombieri 2000, Theorem 12 and the primary abstract | Small-support positivity and variational/negative-spectrum results. | Neither the stated small-support result nor a zero-set matrix can be substituted for the literal cofinal CCM lower bound. Full theorem text was not independently retrieved here; the pinned card supplies its locator. |
| Connes-Consani 2106.01715, Prop.2.1 and Lemma 2.2 | Lower bounded form and its Fourier core. | These give the coarse bound above, not Pminus. |
| Connes-Consani-Moscovici 2310.18423, Theorem 2 / section 4.6 | Semilocal Sonin-space isomorphisms. | Different operator information; no quoted cofinal CCM bottom estimate. |
| Suzuki 2606.09096, Cor.1.2, Thms.1.3-1.4 | Smooth form core, continuity, positive simple-even ground for sufficiently small windows. | The small-window theorem is not a large-window Pminus supplier. |

All rows are [ABSTRACT][PAPER]; project-specialized cofinal supply remains [COFINAL_FAMILY][CONDITIONAL]. This is an audit of the named statements, not a universal assertion that every theorem in the literature has the form `mu >= 0 iff RH`.

An additional recent arXiv preprint, 2608.24827, surfaced in the requested literature search and claims fixed-window certificates beyond the classical small-support range. Its certificates were not independently checked here and are not imported. In particular this verdict does not repeat the shelf's universal claim that no such larger-window claim exists. A fixed-window certificate would still not supply Pminus on an unbounded family.

Any unconditional lower bound mu_{sqrt(m)} >= -exp(-c m), c > 0, on a cofinal family would already force every fixed-window bottom to be nonnegative by (3.27). The finite wide analogue has the same implication by (REC). This explains the load carried by the requested estimate; it is not an argument against searching for its proof.

### Q3(b): can the negative part be super-small relative to the second level?

Not on the literal exhausting family while the second level is positive: Q1.4 gives (-b_m)/s_m >= c/M. If the second level becomes negative, the proposed scale condition fails by spectral ordering. No saturation fit, Fuchs asymptotic, second-level lower bound, or effective knowledge of an off-line zero is required for this conditional-on-not-RH argument. [COFINAL_FAMILY][PAPER]

### Q3(c): trial energy is a separate source theorem

The variational inequality mu_lambda <= R(f) for an admissible nonzero f is immediate from the definition. The R3 report's denial of an upper bound in either direction must not obscure this elementary inequality.

What is not supplied is a sufficiently small **value** of R(k_lambda), or its ratio to the second level. CCM Lemmas 7.2-7.3 concern trial functions and their transforms; Figure 4 compares numerical spectral values with a prolate defect. It is not a theorem bounding QW(k_lambda) by exp(-4*pi*lambda^2+O(log lambda)). In particular, convergence in a transform topology does not by itself control an unbounded Weil form. Fuchs controls a prolate concentration defect; transfer to the Weil trial energy needs a separate exact mechanism. [COFINAL_FAMILY][PAPER]

The spectral split of a_m-b_m is a change of coordinates. The absence of named window/projection-tail terms in that split neither proves nor refutes a source-tail explanation for the same energy.

## Ranked action, discriminators, and alternatives

**First by cost: audit the already cached sign-free and anchor-weighted ledger, with no new eigensolve.** Use the existing (13,120), (23,160), and only those precommitted larger cells that are actually available at intake. Compute Delta, a-b, p, eta and the exact finite C_N at z = 0, 7, i/4, 7+i/4; include removable lattice values. Retain the all-mode energy split. Do not label a few sampled z-values as a supremum certificate. [FINITE_CELL][CONDITIONAL]

Freeze these instrument gates before any new calculation: normalized algebraic residual <= 1e-30; an arithmetic enclosure passes (SF) only if the lower endpoint of (a-b)-Delta*p is nonnegative, and fails it only if the upper endpoint is negative. A straddling interval is INCONCLUSIVE. For a proposed trial-to-ground anchor inference, test sqrt(2eta) <= |q_0|/2 with enclosures. These thresholds classify the instrument and a sufficient finite certificate; they cannot prove or refute an unspecified cofinal Big-O claim.

The cheapest exact discriminator for the claimed polynomial kernel envelope is already the single n = 0 kernel at i/4. The decisive theoretical discriminator for Pminus is a fixed negative Weil test with its (REC) certificate. Such a witness would force an eventual violation, not merely one adverse cell.

Two admissible representations remain, neither promoted here:

1. **Exact anchored error functional:** bound T(v-q)-H_q*T(v-q)(0) directly, preserving its cancellation before using a whole-vector norm. Cache kill-power 9/10; diagnostic cost 2/10; estimated source-proof cost 8/10. A nonvanishing lower envelope on a fixed compact refutes the proposed convergence certificate. No identification of this functional with the desired answer is allowed as its own proof.
2. **Sign-free Ritz with the complete weighted budget:** retain eta, the explicit P59 norm and a source anchor budget. Cache kill-power 8/10; diagnostic cost 1/10; estimated source-proof cost 9/10. The first failure is the source-energy/separation rate or the weighted product, not the finite Ritz algebra. Pminus is an RH-equivalent sufficient route to part of this package, not a cheap weaker lemma.

These are estimated costs, not measured runtimes or new authorizations for large computation.

## Q4. Frozen prediction ledger

Probabilities and event names are preserved. Where the request's parenthetical score exceeds its evidence, the correction is stated rather than changing the event.

```yaml
PREDICTION_FATES:
  P_EPS_INF_BOUNDED_BY_2:
    probability: 0.55
    fate: UNRESOLVED
    scope: FINITE_CELL
    verifier: CONDITIONAL
    note: two_reported_finite_wide_cells_pass_third_pending_and_true_continuum_ratio_not_certified
  P_NSTAR_GROWS_FASTER_THAN_LINEAR:
    probability: 0.65
    fate: UNRESOLVED_AS_ASYMPTOTIC_STATEMENT
    scope: COFINAL_FAMILY
    verifier: CONDITIONAL
    finite_observation: reported_Nstar_over_m_increases_on_three_windows
  P_CCM_HAS_NO_LOWER_BOUND_ON_BOTTOM:
    probability: 0.75
    fate: REFUTED_AS_WRITTEN
    scope: ABSTRACT
    verifier: PAPER
    reason: Proposition_3_3_proves_lower_semiboundedness
    narrower_fact_not_substituted_for_event: no_target_vanishing_negative_large_window_bound_found
  P_ROOF_ACCEPTS_N_OF_M:
    probability: 0.60
    fate: CONFIRMED_AS_SCHEDULE_INTERFACE
    scope: ABSTRACT
    verifier: PAPER
    guard: acceptance_supplies_no_rate_or_test_recovery
  P_MAXDEG600_FLOOR_BELOW_1E-100:
    probability: 0.75
    fate: CONFIRMED_AS_REPORTED_AT_THE_PIN
    scope: FINITE_CELL
    verifier: CONDITIONAL
    independent_rerun: false
  P_WIDE43_PROJECTIVE_ERROR_LE_1E_7:
    probability: 0.67
    fate: PENDING_AT_REQUEST_CUTOFF
    scope: FINITE_CELL
    verifier: CONDITIONAL
  P_WIDE_RESIDUAL_HAS_SOURCE_TAIL_EXPLANATION:
    probability: 0.58
    fate: UNRESOLVED
    scope: COFINAL_FAMILY
    verifier: CONDITIONAL
    note: spectral_split_does_not_test_the_source_tail_identity
  P_CURVATURE_ROUTE_BEATS_WIDE_SCHEDULE_AFTER_PROBES:
    probability: 0.27
    fate: UNRESOLVED
    scope: COFINAL_FAMILY
    verifier: CONDITIONAL
  P_SIGNFREE_PREMISE_STRICTLY_WEAKER_THAN_RH:
    probability: 0.55
    fate: REFUTED_FOR_PMINUS_ON_THE_LITERAL_WIDE_CCM_FAMILY
    scope: COFINAL_FAMILY
    verifier: PAPER
    note: finite_SF_itself_remains_sign_free
  P_COMPACT_TRANSFER_LEAN_READY:
    probability: 0.75
    fate: CONFIRMED_FOR_THE_EXPLICIT_KERNEL_INEQUALITY_ONLY
    scope: FINITE_CELL
    verifier: PAPER
    rejected_extensions:
      - polynomial_in_L_off_axis
      - unweighted_projective_decay_implies_compact_decay
    source_anchor_budget: still_conditional
  P_JUDGE_NAMES_UNCONDITIONAL_LOWER_BOUND:
    probability: 0.15
    fate: REFUTED_FOR_THE_REQUESTED_O_LAMBDA2_TARGET
    scope: COFINAL_FAMILY
    verifier: PAPER
    note: a_coarse_deteriorating_lower_bound_is_not_the_registered_target
  P_NOT_RH_NEGATIVE_PART_IS_LARGE:
    probability: 0.50
    fate: CONFIRMED_CONDITIONALLY_ON_NOT_RH
    scope: COFINAL_FAMILY
    verifier: PAPER
    precise_result: persistent_negative_test_and_bounded_second_level_give_negative_part_ge_c_times_second_when_second_positive
```

The ledger does not rescore unobserved future cells or claim that failure of a sufficient bound falsifies the route.

## CODEX DIRECTIVE — one finite, sign-free theorem only

**Target:** a proposed declaration `signFreeRitz_gap_mul_projectiveDefect_le_rayleighExcess`, reusing an existing equivalent declaration if present.

**Contract:** for a finite real symmetric matrix, an explicitly ordered orthonormal eigenbasis, a unit q, and the first two levels, prove (SF). Also expose its division corollary only under 0 < Delta. Do not put 0 < lambda_1 or 0 < lambda_2 into the head. The proof is the finite weighted-sum argument in S1; no source-specific asymptotic estimate is a hypothesis or an output.

**Required controls:** the negative-bottom equality plant diag(-2,-1); the zero-gap case without division; and the three-level counterexample showing that p -> 0 does not imply eta -> 0. Audit the exact matrix/sector and every printed axiom profile. No submitted job, source edit, or launch is performed by this verdict.

**Validation for any subsequently authorized implementation:**

    WORKDIR: q3.lean.aristotle
      lake env lean Q3/Proofs/RouteB/P59SignFreeRitz.lean
      lake build Q3.Proofs.RouteB.P59SignFreeRitz
    WORKDIR: repository root
      scripts/q3_check.sh Q3/Proofs/RouteB/P59SignFreeRitz.lean

The path is a proposed new target, not an assertion that this file exists. Expected per-export axiom profile: [propext, Classical.choice, Quot.sound], or a documented subset. Any nonstandard axiom is a failure. Success closes the finite sign-free algebra only, not Pminus, the anchor supplier, G3, or RH. If the capability catalog already supplies (SF), stop duplicate construction and cite that declaration.

## Dependency epistemics and closeout

**DOWNSTREAM_CONSUMER:** `Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi`.

**ACTUAL_CONSUMER_REQUIREMENT:** the same real-zero normalized ground family converges locally uniformly to centeredXi; its ground provenance and real-zero premises remain explicit.

**ORIGINAL_REQUESTED_OBJECT:** Pminus, proposed as a strictly weaker internal supplier.

**ORIGINAL_OBJECT_IS:** NOT_NECESSARY for the abstract sign-free inequality or for a direct compact-error proof; RH_EQUIVALENT on the literal exhausting CCM family as proved above.

**KNOWN_WEAKER_INTERFACES:** the exact anchored-functional error tending to zero, or the explicit anchor-weighted Ritz budget, each implying the G3 compact error by S4-S6. Neither is asserted supplied. A lower bound tending to zero for the bottom is not hidden inside either interface by definition.

**FAILURE_TYPE:** INCOMPATIBILITY for the strictly-weaker classification; COUNTEREXAMPLE for `poly(L)` and the rate-free transfer; NO_DERIVATION for the remaining source rates.

**EPISTEMIC_STATUS:** the misclassifications are MATHEMATICALLY_DEAD at their exact theorem shapes. Source rates remain RESEARCH_DEBT. The research route is not declared dead.

**NOVELTY_AXIS:** fixed-test recovery on a moving Galerkin diagonal exposes the asymptotic positivity content without computing the true bottom to relative precision. Exact compact-kernel growth exposes a different, independent loss.

**Reopen triggers:** a correct source-specific proof of the weighted anchored error, a genuinely different non-exhausting consumer with its own exact theorem, or a source estimate that avoids Pminus. Replacing a fixed test by an arbitrary unresolved spectrum is not a reopen trigger. Further finite successes alone do not overturn Q1's implication.

**What became smaller:** the alleged weaker premise is classified by two fixed test functions and one possible negative witness; the compact-transfer debt is the explicit weighted product, not an unexplained continuity claim.

**What was killed:** Pminus-as-strictly-weaker, the signless multiplication of an upper Rayleigh ratio, `p -> 0 iff eta -> 0`, a polynomial-in-log-length complex kernel bound, and sampling-as-anchor-lower-bound.

**What must not be repeated:** confusing a sign-free finite identity with a weak global assumption; calling observed spectral saturation a continuum certificate; using eigenvalue decay as a rate for eigenvector error; or reading a spectral energy decomposition as proof that physical source tails do not exist.

**Current smallest source gap:** an independently proved source-specific anchor-weighted ground/trial error bound on the fixed schedule. The finite transfer inequality is not that supplier.

**Progress class:** FALSIFICATION_PROGRESS. **Cognitive operator:** COUNTEREXAMPLE_HUNT. **Route score:** 4. No source supplier count or route state changed.

## Evidence and verification handoff

Repository evidence is pinned at `f7f6b91cdec7f8362a858f7a7974f685d24e78db` unless the request specifies its shelf base. The request's SHA-256 and Git-object SHA-1 were independently recomputed from the fetched UTF-8 payload; the receipt is 11666 bytes, 117 LF characters, final LF present. Only this expected verdict document is written; the shared progress log, queue, old verdicts and Lean tree are not edited.

Primary paper checks used CCM 2511.22755, pp.6,9,11,32-33; Connes-Consani 2106.01715, Proposition 2.1 and Lemma 2.2; Suzuki 2606.09096, Corollary 1.2 and Theorems 1.3-1.4; and Connes-Consani-Moscovici 2310.18423, its Sonin-space theorem. The relevant CCM and Suzuki pages were visually checked as PDF screenshots. The Yoshida and detailed Bombieri locators are supplied by the pinned source card; their full scans were not independently retrieved. Q1's finite moving-window recovery and S4-S6 are this verdict's paper derivations, not claimed Lean results or quotations from those papers.

Write verification: read this complete file back at the returned commit; confirm the first-line operative class, this request lock, final LF and unchanged probabilities. The GitHub commit/blob receipt is returned with the verdict delivery; it is not embedded recursively in its own content. No Lean gate applies to this documentation-only commit. A clean write confirms materialization, not an additional kernel theorem.
