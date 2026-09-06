# STATUS: TRY_SEMISIGN_CERTIFIED_INVERSE_SERIES_AND_TRACE_DOMAIN_REPAIR
```yaml
PRIMARY: TRY_SEMISIGN_CERTIFIED_INVERSE_SERIES_AND_TRACE_DOMAIN_REPAIR
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_SEMISIGN_CERTIFIED_INVERSE_SERIES_AND_TRACE_DOMAIN_REPAIR
REQUEST_ID: REQ-2026-09-06-SEMISIGN
BOUNDARY_ID: GOAL058_SEMILOCAL_SIGN_MECHANISM_AND_PRIME_ALLOCATION
RESULT:
  Q1: PARTIAL_WITH_PRECISE_REMAINDER
  Q2: OBSTRUCTION_NAMED
  Q3: COMPUTATION_SPECIFIED
REQUEST_LOCK:
  COMMIT: 2482f3f528f9820d95b15d733d7794a508b681f7
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_SEMILOCAL_SIGN_MECHANISM_2026-09-06.txt
  GIT_BLOB: 4a57a4b0e8ca9579b9ba2076bd70ed5319254e13
  SHA256: b3bc14cfc6b043dc4d2b252e9c22ebd3a7b5fee6de82690850929d86ba211a91
  BYTES: 9241
  LINES: 84
  FINAL_LF: true
  FETCHED_UTF8_REENCODING_HASHES_INDEPENDENTLY_RECOMPUTED: true
PARENT_LOCK:
  COMMIT: 3242ada9ee58c0716d64192c9749fcfa742af806
  GIT_BLOB: 7b4e6562c358902eb1c7204b1fcded7a2ee6b91d
  SHA256: ece45e22518a1395927e55e64ab9945c80bd597fb8707015e55de9657c94416d
  MOUNTED_BYTES_HASHES_RECOMPUTED: true
PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_SECOND_EXPRESSION
  SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
  TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false
EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SEMILOCAL_SIGN_MECHANISM_2026-09-06.md
FROZEN_CUTOFF_CLASS_SIGN_PROVED: false
AUXILIARY_SIGN_THEOREM:
  status: PROVED_ON_CLASS
  class: each_fixed_finite_dimensional_highly_modulated_pole_null_packet
  support: may_have_log2_less_than_L_le_log3_and_nonzero_prime2_correlation
  cutoff: sufficiently_large_packet_dependent_Sonin_cutoff
  not_the_frozen_lambda1_table: true
NEW_PAPER_RESULTS:
  - exact_weighted_angle_energy_criterion_with_full_tail
  - one_sided_Gram_inverse_polynomial_enclosures_at_p2
  - finite_test_space_matrix_sign_certificate_with_explicit_inverse_tail
  - high_modulation_large_cutoff_sign_theorem
  - explicit_wide_positive_bump_positive_E_theorem
  - translation_invariance_and_exact_pole_null_two_bump_falsifier
  - common_model_orthogonality_of_matched_window_and_Sonin_projections
  - calibrated_atom_contrast_with_explicit_archimedean_error
SOURCE_CORRECTIONS:
  CCM23_Def4_5_Thm4_6_are_not_a_commuting_prolate_operator_theorem: true
  C99_Theorem5_as_printed_first_has_positive_characteristic_scope: true
  C99_also_computes_a_harmonic_measure_limit_beyond_Poisson_inclusion: true
PRIME_ATOMS_ASSIGNED_SEPARATELY_TO_N_AND_E: false
CONTACT_ALLOCATION_OF_ANGLE_PART_PROVED: false
OBSERVER_PARALLEL_TABLE_READ: false
NUMERICAL_RUN_PERFORMED: false
LEAN_EDIT_PERFORMED: false
ARISTOTLE_SUBMISSION: false
REPOSITORY_WRITE_SCOPE: EXPECTED_VERDICT_DOCUMENT_ONLY
CLOSES: [REQ-2026-09-06-SEMISIGN]
CLOSES_ANALYTIC_RH_SUPPLIERS: []
OPENS: []
SCOPE: ABSTRACT
VERIFIER: PAPER
INDEPENDENT_KERNEL_VERIFICATION: false
NOVELTY_IN_THE_LITERATURE: not_claimed
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
NEGATION_OF_RH_CLAIM: false
```

## 0. Decision and source boundary

The full sign on the reference-cutoff, pole-null log-3 class is not proved. The explicit semilocal construction is retained. The new computational mechanism is a **one-sided convergent inverse series**, with a remainder controlled by an independently positive archimedean trace. It yields a matrix certificate on any prescribed finite test space, not merely a list of individually tested vectors. No such matrix has been evaluated in this session.

A separate sign theorem is proved below on finite-dimensional high-frequency packets with sufficiently large Sonin cutoffs. This is a real nonempty, prime-active class, but it does not certify the table at cutoff 1 and does not exhaust the full Weil test class.

The global trace question has more source content than the request reports: Connes computes a harmonic-measure limit in addition to the Poisson inclusion. Conversely, the literal compact/compact-Fourier intersection used first in the function-field argument cannot simply be specialized to the archimedean semilocal Hilbert space.

The separate atomic allocation remains undecided. Section 6 gives a finite, calibrated contrast and a controlled inverse approximation for measuring it. No finite table is represented as a theorem about distributional atoms.

### Source ledger

[C20] Connes--Consani, arXiv:2006.13771v1: Theorem 4.7, (83)--(84), pp.27--28; Proposition 5.5, (103)--(104), pp.33--34; Lemma 6.10 and Theorem 6.11, (140)--(143), pp.48--49; Appendix F, pp.53--55. The source provides an archimedean test-operator estimate with additional moment and support conditions, not its semilocal analogue.

[C23] Connes--Consani--Moscovici, arXiv:2310.18423v2: Definition 2.2, p.6, is explicitly formal as to operator domain; Definition 4.5 and Proposition 4.6, pp.21--22; Proposition 4.7, (57)--(59), pp.22--23; Theorem 4.6, p.23. The latter identifies Sonin spaces by a bounded invertible map, not an isometry. These are the v2 locators used here.

[C99] Connes, arXiv:math/9811068v1: Theorem 4, p.31; Theorem 5 and condition (a), p.42; (21)--(26), p.43; Lemma 3 and (27)--(29), pp.44--45; number-field modification, pp.45--47. The printed Theorem 5 first treats positive characteristic. The following discussion changes the archimedean cutoff construction.

[C26] Connes, arXiv:2602.04022v1: (19), p.31; (22), p.32; endnote 11, (29)--(32), p.36. The fixed-cutoff trace identity is imported in its stated smooth-test trace sense, not obtained by deleting the o(1) in C99.

[C21] Connes--Consani, arXiv:2106.01715v1: Proposition 2.1, (2.11), pp.4--5, and the experiments in Sections 2.2--2.3, pp.5--7. The latter are not imported as analytic sign theorems.

[P] The pinned SEMILOCAL verdict and its mounted 44,869 bytes, whose hashes match. [IC] The independent-check document at the request pin was read, including the locator corrections. It is a review report, not a replacement for the primary definitions. [Q] The source form and canonical cutoff definitions specified in the request retain their meanings.

All computations newly proved below are our PAPER derivations from these specified objects. No priority claim is made. The unrelated historical attachments do not supply the current sign.

## 1. Q1(a): the exact sign condition and what the prolate citation does not supply

Write a log test as v and its multiplicative version as k_v(u)=v(log u). Set

\[
 f_v=k_v*k_v^*,\quad T_v=\vartheta(k_v),\quad
 n_\lambda(v)=\|T_v\mathsf S_{S,\lambda}\|_{HS}^2,\quad
 e_\lambda(v)=E_{S,\lambda}(f_v).
\]

The nonnegative statement is about f_v, not an arbitrary k. Put ell=2 log lambda for equal position/Fourier cutoffs. The parent identity gives

\[
 L_S(f_v)=n_\lambda(v)-e_\lambda(v),\qquad
 e_\lambda(v)=\operatorname{Tr}(T_v^*T_vD_{S,\lambda})-\ell\|v\|_2^2.
\tag{1}
\]

For S={infinity,2} and support diameter at most log 3,

\[
 L_S(f_v)=\mathcal D(v)-c_A\|v\|_2^2
 -2w_2 C_v(a),\quad a=\log2,\quad w_2=\log2/\sqrt2,
\tag{2}
\]
\[
 \mathcal Q(v)=L_S(f_v)+P_{02}(v).
\]

At the endpoint L=log3 the smooth autocorrelation at log3 vanishes; no prime 3 is silently discarded. All higher powers of 2 are outside this support. The reference table below is registered at lambda=1 unless explicitly stated otherwise. Its cutoff must be recorded: changing lambda changes both n and e, although L_S is fixed.

### Lemma 1: weighted angle criterion [ABSTRACT][PAPER]

Diagonalize each two-dimensional parent block D_n. Let a_n=|alpha_n|, and let e_n^+,e_n^- be its orthonormal eigenvectors for +a_n,-a_n, computed from the matrix in parent (6). Then

\[
 e_\lambda(v)=\sum_n a_n
 (\|T_ve_n^+\|_2^2-\|T_ve_n^-\|_2^2)-\ell\|v\|_2^2.
\tag{3}
\]

Consequently the exact sufficient and necessary angle-data inequality on a declared class C is

\[
 \sum_n a_n\|T_ve_n^+\|^2
 \le \sum_n a_n\|T_ve_n^-\|^2+\ell\|v\|^2,
 \qquad v\in C.
\tag{4}
\]

For the pole-retaining comparison, add P_02(v) to the right side. This is an explicit weighted comparison of the dilation profiles of the two block vectors, not a consequence of the unordered eigenvalues +/-a_n.

**Proof.** The source block is self-adjoint and has the displayed two eigenvalues. The diagonal entries of T_v^*T_v in that basis are squared norms. Summing its trace against D gives (3). In the ordinary smooth-test trace-class realization used for the parent split, the absolute sum of these diagonal entries weighted by a_n is finite; it is bounded by the trace norm of T_v^*T_vD. This justifies (3) on that domain. If a different regularized realization is used, this argument must be replaced by its corresponding trace theorem, not assumed. Rearranging proves (4). QED.

There is no useful class obtained by requiring T_ve_n^+=0 for every positive direction: a nonzero compact smooth v has a nonzero-a.e. entire Fourier multiplier, so T_v is injective on L2. Such a requirement would force the nonzero e_n^+ to vanish. The required cancellation is **integrated**, not blockwise annihilation.

### Source repair: commuting with Fourier grading is not commuting with both cutoffs

C23 Definition 4.5 defines the Sonin space; Theorem 4.6 proves its isomorphism. Neither states the proposed self-adjoint prolate/domain/ordering theorem for both literal cutoff projections. The formal prolate operator in Definition 2.2 has an explicitly unresolved domain issue in the general cyclic-pair setting. Its grading commutation does not establish the missing cutoff commutation or the ordering of the test-space remainder. This source claim in Q1(a) is not imported.

Even a proven operator commuting with both projections would label the blocks without determining the profiles T_ve_n^+ versus T_ve_n^-. That is exactly where sign would still have to enter.

### The precise analogue of the single-bad-mode argument

Suppose a support-preserving pole-removal parametrization v=A h has been proved, and its explicit remainder operator on h is

\[
 e_\lambda(Ah)=d\langle h,(K-I)h\rangle,\quad d>0,
\]

with K self-adjoint. If K has a unit eigenvector zeta with eigenvalue 1+b, b>0, and K on zeta-perp is at most 1-c, c>0, then for a unit constraint vector u,

\[
 \langle u,h\rangle=0\ \Longrightarrow\
 \langle h,(I-K)h\rangle
 \ge\big((b+c)|\langle zeta,u\rangle|^2-b\big)\|h\|^2.
\tag{5}
\]

Thus |<zeta,u>|^2>=b/(b+c) is sufficient. Proof: K<=(1-c)I+(b+c)|zeta><zeta| and, on u-perp, |<zeta,h>|^2<=(1-|<zeta,u>|^2)||h||^2. Substitution gives (5).

This finite-rank inequality is proved here. For the semilocal target, the representation by K, its tail bound and the overlap are **not** supplied by C23. C20 supplies their archimedean counterpart, with its own support and extra mean condition. Its numerical spectral values cannot be reused as semilocal data.

## 2. Q1(b): a convergent sign certificate and an actual nonempty sign class

### Lemma 2: one-sided inverse polynomials [ABSTRACT][PAPER]

Take one prime p=2, r=1/sqrt2, a=log2, U=U_a. Let P0 be the archimedean Sonin projection at the SAME lambda, H0=ran P0, and B=I-rU. Then

\[
 G=P0B^*BP0|_{H0}=(1+r^2)(I-qA),\qquad
 A=\tfrac12P0(U+U^*)P0|_{H0},\quad \|A\|\le1,
\]
\[
 q=\frac{2r}{1+r^2}=\frac{2\sqrt2}{3}<1,\qquad a_* =1-r>0.
\tag{6}
\]

For integer d>=0 define

\[
 R_d=\frac1{1+r^2}\sum_{j=0}^{2d+1}q^jA^j,\qquad
 \varepsilon_d=\frac{q^{2d+2}}{a_*^2}.
\]

Then

\[
 \boxed{0<R_d\le G^{-1}\le R_d+\varepsilon_d I.}
\tag{7}
\]

**Proof.** On the spectral interval x in [-1,1], the finite sum is
(1-(qx)^(2d+2))/(1-qx)>0. Its difference from 1/(1-qx) is
(qx)^(2d+2)/(1-qx)>=0 and is at most q^(2d+2)/(1-q). Multiplying by (1+r^2)^(-1) and using (1+r^2)(1-q)=(1-r)^2 proves (7) by continuous functional calculus. No Weil lower bound is used. QED.

Set C_v=T_v B|_{H0}. Its Hilbert--Schmidt norm is known from the archimedean positive trace:

\[
 m(v):=\|C_v\|_{HS}^2=n_\infty(Bv),
 \qquad Bv=v-rU_av.
\tag{8}
\]

Here the infinity subscript denotes the single-place Sonin construction, not a limiting cutoff. C20 Theorem 4.7 evaluates this functional on compact smooth tests of arbitrary support; the SMALL-support sign theorem is not needed for (8).

The parent projector gives

\[
 n_\lambda(v)=\operatorname{Tr}(C_vG^{-1}C_v^*).
\]

Define the finite sum of explicit operator moments

\[
 n_d(v)=\frac1{1+r^2}\sum_{j=0}^{2d+1}q^j
                 \operatorname{Tr}_{H0}(A^jC_v^*C_v).
\]

Equation (7) gives the **one-sided** error ledger

\[
 \boxed{n_d(v)\le n_\lambda(v)\le n_d(v)+\varepsilon_dm(v),}
\]
\[
 \boxed{n_d(v)-L_S(f_v)\le e_\lambda(v)
          \le n_d(v)+\varepsilon_dm(v)-L_S(f_v).}
\tag{9}
\]

This retains the coupled finite-Euler inverse instead of replacing n_lambda by a large multiple of n_infinity. It gives independent upper and lower bounds, not a fitted law.

### Corollary: finite-space sign, including all cross terms [FINITE_CELL][PAPER]

For fixed compact smooth tests v_1,...,v_J with support diameter <=log3, polarize n_d, m, and L_S to Hermitian matrices N_d,M,L on their coefficient space. Then

\[
 N_d\preceq N\preceq N_d+\varepsilon_d M.
\]

For coefficients satisfying exact moment constraints Rc=0,

\[
 c^*(N_d+\varepsilon_dM-L)c\le0\quad\forall c\in\ker R
\tag{10}
\]

certifies e_lambda(v_c)<=0 for EVERY v_c=sum c_jv_j in that constrained finite space. For e<=P_02 replace L by L+P, with P the exact polarized pole matrix.

**Proof.** Apply (9) to v_c for arbitrary complex c. A Hermitian quadratic inequality for every c is precisely the Loewner matrix order. Restriction to ker R preserves it. QED.

A check of the separate diagonal values is not (10). A bound on the last computed angle alone is also insufficient: it does not bound its infinitely many weighted overlaps.

**Implementation boundary.** Each moment above is still an operator trace/integral. A finite-grid implementation must enclose its quadrature and projection errors. The known bound (7) closes the inverse-series tail, NOT all discretization tails. If the matrix moment errors have total operator-norm enclosure delta, add delta*I to the upper matrix in (10). The first unproved frozen-cutoff inequality is exactly that upper matrix <=0, or its infinite test-space limit. Neither is asserted here.

For independent finite evaluation, choose finite-rank projections F_M increasing to I on H0. If X=C_v, tau_M=||X(I-F_M)||_HS and H=G^{-1}, then

\[
 |\operatorname{Tr}(XHX^*)-\operatorname{Tr}(XF_MHF_MX^*)|
 \le a_*^{-2}(2\sqrt{m(v)}\,tau_M+tau_M^2).
\tag{11}
\]

This follows by writing X=XF_M+X(I-F_M), expanding and using the Hilbert--Schmidt Cauchy--Schwarz inequality. Moreover tau_M^2=m(v)-sum_{j<=M}||Xe_j||^2. Thus a certified upper bound for m(v) and lower bounds for that partial sum give a valid tail bound; no decay fitted to angle samples is needed. Approximate actions of A in the polynomial require their own norm enclosures. Never trace the infinite identity component separately from its Sonin cancellation.

### Lemma 3: sign on finite high-frequency packets at large cutoffs [COFINAL_FAMILY][PAPER]

Fix log2<L<=log3 and a finite-dimensional nonzero H subset C_c^infinity((-L/2,L/2);C). Put M_j=2pi*j/log2 and

\[
 V_jh=M_j^{-2}(\partial_x^2-1/4)(e^{iM_jx}h(x)).
\]

Every V_jh is compact smooth and satisfies A_+(V_jh)=A_-(V_jh)=0. There exists j0 such that for every j>=j0 there is a finite lambda0(j,H) for which

\[
 \boxed{e_\lambda(V_jh)\le-\tfrac12L_S(f_{V_jh})<0}
\tag{12}
\]

for all nonzero h in H and all lambda>=lambda0(j,H).

**Proof.** Integration by parts gives the two pole conditions. Expanding,
V_jh=e^{iM_jx}[-h+(2i/M_j)h'+M_j^{-2}(h''-h/4)]. On the finite-dimensional H the bracket converges to -h in every Schwartz seminorm uniformly on its unit sphere.

The archimedean multiplier in [Q,C21 (2.11)] is
m_A(t)=Re psi_d(1/4+it/2)-log pi. Its standard digamma asymptotics imply m_A(t)=log|t|+O(1) as |t| tends to infinity, and |m_A(t)|<=C log(2+|t|). For fixed Fourier variable z,
m_A(z+M_j)/log M_j tends to 1. The bound C'(1+log(2+|z|)) and the rapid decay of the Fourier transforms of a finite basis justify dominated convergence on each matrix entry. Consequently

\[
 L_S(f_{V_jh})/\log M_j\longrightarrow\|h\|_2^2
\]

uniformly on the unit sphere of H: the prime-2 shift term has bounded operator norm 2w_2 and disappears after division by log M_j. Thus this quadratic form is strictly positive on V_jH for j>=j0.

For a fixed such j, the Sonin projections S_lambda decrease strongly to zero as lambda tends to infinity: their ranges decrease, and every common-range vector vanishes on x<=log lambda for every lambda, hence is zero. For any fixed compact test v, T_vS_1 is Hilbert--Schmidt by the established trace domain. Therefore ||T_vS_lambda||_HS tends to zero, by finite-rank approximation of T_vS_1 and strong convergence of S_lambda. Polarization gives entrywise convergence of the finite matrix N_lambda on V_jH, hence convergence in matrix norm. Choose lambda0 so that N_lambda<=L/2 as forms on that space. Equation (1) proves (12). QED.

This does not avoid primes by support. Taking H to contain a smooth positive bump of full diameter L gives C_h(log2)>0. The chosen modulation has exp(iM_j log2)=1, and C_{V_jh}(log2) tends to C_h(log2), so the prime term is genuinely nonzero.

**Scope:** (12) changes the Sonin cutoff. It proves neither e_1<=0 on the table class nor positivity on all pole-null tests. No uniform lambda0 for the entire infinite-dimensional class is obtained. This is the nonempty sign class established here, not a claim that it is mathematically maximal. The frozen-cutoff part of Q1 remains PARTIAL.

## 3. Q1(c): retaining the pole term

Write C(v)=integral v(x)cosh(x/2)dx and S(v)=integral v(x)sinh(x/2)dx. Direct expansion gives

\[
 P_{02}(v)=2|C(v)|^2-2|S(v)|^2.
\tag{13}
\]

Thus there is no universal easier/harder comparison. On even tests it is nonnegative, so e<=P_02 is weaker than e<=0. On odd tests it is nonpositive, so e<=P_02 is stronger. On the full complex class it is indefinite. Both A_+=A_-=0 imply P_02=0; a single vanished pole functional also suffices for that equality, but is a different test class.

The matrix P in (10) keeps both mixed terms. Dropping the negative odd square is not an allowed simplification. The largest class is not obtained merely by forgetting the pole-null conditions.

## 4. Q1(d): explicit tests and analytic checks before the unseen table

Fix a=log2 and the even smooth probability bump

\[
 \eta(x)=Z^{-1}\exp[-1/(1-x^2)]\mathbf1_{|x|<1},\quad
 \eta_\delta(x)=\delta^{-1}\eta(x/\delta).
\]

All normalizations below are integrals of displayed functions, not fitted constants. Choose

\[
 \delta_0=(\log3-\log2)/8,\quad
 w=(\partial_x^2-1/4)\eta_{\delta_0},\quad
 v_\pm(x)=\frac{w(x-a/2)\pm w(x+a/2)}{\sqrt2\|w\|_2},
\tag{14}
\]

and v_i with +i instead of +. Their disjoint supports have diameter a+2delta0<log3; both pole functionals vanish. Their correlations at a are exactly +1/2,-1/2,0, respectively. This follows by shifting the disjoint bumps and integration by parts for the pole conditions. No equality for their Sonin cross terms is assumed.

The preselected falsifier is v_+. It maximizes the **positive prime-2 correlation** within this two-bump phase family. It is a candidate, NOT a proved maximizer of e/n. The denominator n_1(v_+) is strictly positive: T_{v_+} is injective, and the Sonin range is nonzero. The registered ratio interval is in section 8.

### Translation check

For every c, T_{U_cv}=U_cT_v, so n_lambda(U_cv)=n_lambda(v). L_S is also translation invariant. Therefore

\[
 \boxed{e_\lambda(U_cv)=e_\lambda(v).}
\tag{15}
\]

In particular single narrow bumps centered at +a/2 and -a/2 have IDENTICAL e and n. Different reported signs would be a discretization/source bug, not prime sensitivity. Two-bump interference, not moving a lone bump, is the meaningful test.

### Explicit wide-bump theorem, not just a forecast

Let delta=1/1000, b>=3, d=b-delta, and

\[
 h_d(x)=\cos(\pi x/(2d))\mathbf1_{|x|\le d},\qquad
 v_b=(h_d*\eta_\delta)/\|h_d*\eta_\delta\|_2.
\]

This is a nonnegative smooth compact test of support diameter 2b. Since h_d is in H1,

\[
 \|v_b'\|_2\le\frac{\pi}{2b-\delta(2+\pi)}.
\]

Indeed convolution does not increase ||h_d'||_2, and its L2 norm is at least ||h_d||_2-delta||h_d'||_2 by the translation estimate. Use ||h_d'||_2/||h_d||_2=pi/(2d). The parent bound integral t^2a(t)dt<=18 then yields

\[
 L_S(f_{v_b})\le-c_A+
 18\left[\frac{\pi}{2b-\delta(2+\pi)}\right]^2<0.
\tag{16}
\]

The strict sign follows without numerical quadrature: c_A>5, pi<22/7, and at b=3 the second term is less than 5 by rational comparison; it decreases with b. Hence

\[
 e_\lambda(v_b)=n_\lambda(v_b)-L_S(f_{v_b})>n_\lambda(v_b)>0.
\tag{17}
\]

These wide bumps are outside the log-3 target class and are not pole-null. They cannot refute its sign. They are an exact positive-E control for the table.

For completely reproducible canonical cutoffs, let q(t) equal 1 for t<=0, 1-10t^3+15t^4-6t^5 on [0,1], and 0 for t>=1. Set q_c(t)=q((t-1/100)/(98/100)) and

\[
 \chi_R(x)=(q_c*\eta_{1/200})(|x|-R),\qquad v_R=\chi_R f_0,\quad R=1,2.
\]

This is an explicit instance of the committed smooth cutoff construction in [Q], with the same derivative bounds. Those supports also exceed the target window. The parent eventual radical argument does NOT fix R=1 or R=2; their signs below are forecasts, not consequences of an unspecified sufficiently-large-R theorem.

## 5. Q2: the global image, the trace limit, and the failed specialization

### Q2(a): condition (a), with its actual scope

In C99 Theorem 5, p.42, condition (a) is: for each compact smooth test h on C_k,

\[
 \operatorname{Tr}(Q_\Lambda U(h))=
 2h(1)\log'\Lambda+
 \sum_v\int_{k_v^*}'\frac{h(u^{-1})}{|1-u|_v}\,d^*u+o_h(1),
 \quad\Lambda\to\infty.
\tag{18}
\]

The prime on the integral is its specified additive-Fourier normalization. The quantifier is a limit for each fixed h, not an unspecified uniform error over all h. The theorem first states this for positive characteristic. Number fields require the prolate modification discussed on pp.45--47; exact simultaneous compact supports cannot simply be kept at the real place.

After the unitary/scaling dictionary, define the actual trace error

\[
 r_\Lambda(h)=\operatorname{Tr}(Q_\Lambda U(h))
 -2h(1)\log'\Lambda-\sum_v\int' h(u^{-1})/|1-u|_v\,d^*u.
\]

The missing statement is r_Lambda(h)->0 in this specified construction. The inclusion Q'_Lambda,0<=W_Lambda only gives positivity and support of a DIFFERENCE projection. It does not compute r_Lambda. For example Q'=0 also satisfies that inclusion, but leaves the full 2f(1)log'Lambda window trace. Thus inclusion alone cannot supply a finite limiting arithmetic distribution. The two trivial-character/pole contributions must be retained when comparing Q_Lambda with its zero-mass version Q_Lambda,0.

**Important correction to the request:** C99 does not stop at Poisson summation. Lemma 3, pp.44--45, computes, in its stated function-field setting and without assuming zero reality in the calculation, a limit with the harmonic measure of each zero on the critical line. The passage to number fields is discussed afterwards. Thus "nothing unconditionally known beyond Poisson" is not an accurate summary of that source.

The distinction is substantive. For a point sigma+i gamma, sigma!=0, its harmonic measure on the line has density

\[
 \frac1\pi\frac{|\sigma|}{(t-\gamma)^2+\sigma^2}\,dt.
\]

Its Fourier mode is exp(i gamma x-|sigma||x|), not exp((sigma+i gamma)x). For the symmetric pair the latter arithmetic expression involves cosh(sigma x), not exp(-|sigma||x|). These differ for x!=0. Positivity of the harmonic-measure limit therefore does not identify it with the arithmetic evaluation. This is the exact comparison to prove, not a reason to abandon the target.

The source relates (18) to RH; that relationship is reported with the correct scope, not used as a kill. The unproved task in the number-field program is the arithmetic trace comparison for its specified approximate image, not the existence of a positive difference projection by itself.

### Q2(b): there is no literal finite-Euler replacement with the stated properties

On the K_S-invariant semilocal Hilbert space with the exact cutoffs,
ran P_Lambda intersect ran Q_Lambda={0} (parent Lemma 2). Thus a proposed Q'^S built from the exact common range and transported by the bounded finite-Euler map is zero. Its trace is explicitly zero, but then the window-minus-image trace retains the logarithmically growing window term, not N_S-E_S.

There is a second independent failure. The finite-Euler map

\[
 J_S=\sum_{n\in M_S}n^{-1/2}U_{-\log n}
\]

preserves an upper cutoff but not a two-sided multiplicative window. For S={infinity,p}, take any nonzero smooth h supported in an interval of width <log p, inside the upper cutoff. At points x=x0-j log p with h(x0)!=0, precisely one translated copy contributes, so

\[
 (J_Sh)(x0-j\log p)=p^{-j/2}h(x0)\ne0
\]

for arbitrarily large j. The left tail does not vanish. One may impose finitely many moment constraints on h without destroying this disjoint-copy argument. Also M_S is infinite even for a finite set of primes. It is not a finite Euler sum.

Therefore the global Poisson image E(B_Lambda,0), the finite-Euler image J_Sh and the Sonin image B_SH0 are three different objects. Replacing the first by either of the last two does not specialize (23). Truncating J or projecting its image into a window defines a new approximation whose image error and Gram matrix must be proved; no exact trace formula for that replacement is supplied by the shelf. This is the named failed step, not a theorem that no useful semilocal approximation can exist.

### Q2(c): an exact relation in the common log model, but not the desired identification

Write W_Lambda=1_{[-log Lambda,log Lambda]} on the log line, and R_Lambda=W_Lambda-Q'_Lambda,0 whenever the latter is a genuine subprojection on that space. Then 0<=R_Lambda<=W_Lambda.

The matched semilocal Sonin projection S_{S,Lambda} has range supported in x>=log Lambda. Hence, up to a measure-zero endpoint,

\[
 \boxed{W_\Lambda S_{S,\Lambda}=0,
        \qquad R_\Lambda S_{S,\Lambda}=0.}
\tag{19}
\]

Proof: the support intervals are disjoint; R is dominated by W. If both projections are nonzero they cannot dominate one another: apply a proposed order to a unit vector in the other orthogonal range. This is a precise common-model obstruction to identifying the two positive differences. It does not claim that their original representations have a canonical identification beyond the stated log transport.

With a fixed Sonin cutoff 1 and a moving window Lambda, the supports overlap; (19) no longer applies. No general order in that comparison is supplied. The traces arise from different constructions and need a proved comparison, not matching names S_Lambda and S_S.

## 6. Q3: singular parts, controlled moments and a calibrated atom experiment

### 6.1 What is rigorously fixed already

Let F(t)=f(e^t) be a log test. With a(t)=e^{-t/2}/(1-e^{-2t}), define the difference-energy distribution

\[
 \langle\mathfrak D,F\rangle=
 \int_0^\infty a(t)[2F(0)-F(t)-F(-t)]dt.
\]

The complete local distribution is

\[
 \boxed{L_S=\mathfrak D-c_A\delta_0
 -\sum_{p\in S_f,j\ge1}(\log p)p^{-j/2}
                       (\delta_{j\log p}+\delta_{-j\log p}).}
\tag{20}
\]

Away from 0 and the prime powers its density is -a(|t|). At 0 it is a regularized singular distribution, not a continuous function. The equivalent subtraction convention is

\[
 -c_0 F(0)-\int_0^\infty a(t)
       [F(t)+F(-t)-2e^{-t/2}F(0)]dt,
\quad c_0=\gamma_E+\log4\pi.
\]

Both conventions agree since 2 integral a(t)(1-e^{-t/2})dt=log2+pi/2. Thus c_A=c_0+log2+pi/2, exactly. An isolated delta coefficient is meaningless unless the finite-part subtraction convention is fixed.

Write Aang_lambda=Tr(theta(f)D_S) as a distribution. The established split gives

\[
 E_S=Aang_\lambda-\ell\delta_0,
 \qquad N_S=Aang_\lambda+\mathfrak D-(c_A+\ell)\delta_0
           -\sum_{p,j}w_{p^j}(\delta_{\pm j\log p}).
\tag{21}
\]

The sum of +/- Diracs in (21) has the meaning in (20). The explicit cutoff contact in E is -ell delta_0. Any additional contact, prime atoms or singular regular parts of Aang remain to be determined. Compactness of the angle operator does not prove that its trace distribution is a continuous function; the parent explicitly left that regularity unproved.

Thus if c_N(a),c_E(a) exist as isolated atomic coefficients, then

\[
 c_N(j\log p)-c_E(j\log p)=-(\log p)p^{-j/2}.
\tag{22}
\]

No individual coefficient has been computed in this document. Prime dependence of B and G is not such a computation. Also a negative off-identity atom in N would not contradict positive type: 2delta_0-delta_a-delta_-a yields ||U_av-v||^2>=0 on squares.

### 6.2 The proposed r-expansion: exact, but not a coefficient read-off

For B_r=I-rU_a and P0 fixed, direct differentiation of the corrected range projection at r=0 gives

\[
 S'_0=-(I-P0)U_aP0-P0U_a^*(I-P0).
\tag{23}
\]

Proof: G_r=I-rP0(U_a+U_a^*)P0+r^2I, so (G_r^{-1})'_0=P0(U_a+U_a^*)P0 on H0. Differentiate B_rP0G_r^{-1}P0B_r^* and collect the off-diagonal terms. QED.

The first derivative is already a pair of projection commutators. It is not a scalar multiple of U_a+U_a^*, and its trace distribution cannot be identified with Diracs at +/-a merely by looking at the phase exp(i a t). Higher orders retain the same noncommutative compressed products. Equation (7), which converges at the physical r=1/sqrt2, is preferable to a formal small-r expansion.

The calculation specified for N is the finite polynomial moment sum n_d in section 2, with upper error epsilon_d*m(v), plus independently enclosed quadrature/basis errors (11). E can then be evaluated as n-L_S. That use of the proved identity is legitimate evaluation, but **N-E=L_S is then tautological as a discretization check**. An independent check must compute E from the angle trace or independently test the projection/action; translation invariance (15) is another non-tautological check.

### 6.3 Atom contrast on finite smooth tests

Take a real nonnegative u in C_c^infinity((-1,1)) with ||u||_2=1, for example eta/||eta||_2. Put u_delta(x)=delta^{-1/2}u(x/delta), and let gamma_delta be its autocorrelation. It has height 1 at 0, support [-2delta,2delta], and integral delta*||u||_1^2.

For a=j log p>0 isolated from the other prime locations, take delta small enough that [a-2delta,a+2delta] misses 0 and all other locations. Define

\[
 z_+=u_\delta+U_a u_\delta,\quad z_-=u_\delta-U_a u_\delta,
\]
\[
 A_N(\delta,a)=\frac{n_\lambda(z_+)-n_\lambda(z_-)}4,
 \qquad A_E(\delta,a)=\frac{e_\lambda(z_+)-e_\lambda(z_-)}4.
\tag{24}
\]

Their common distribution test is
F_delta(t)=[gamma_delta(t-a)+gamma_delta(t+a)]/2. Its value at 0 is zero. Substitution in (20) gives the **exact calibration**

\[
 \boxed{A_N(\delta,a)-A_E(\delta,a)
 =-w_{p^j}-I_{a,\delta},\qquad
 I_{a,\delta}=\int_{a-2\delta}^{a+2\delta}
             a(t)\gamma_\delta(t-a)dt\ge0.}
\tag{25}
\]

Here the same letter a in a(t) denotes the already fixed archimedean density, not the shift parameter; I is unambiguous from its formula. In particular

\[
 0\le I_{a,\delta}\le
 \delta\|u\|_1^2\sup_{|t-a|\le2\delta}a(t).
\tag{26}
\]

Proof: expand the two autocorrelations; their central terms cancel. The source contact vanishes and exactly the selected pair of prime atoms survives. The continuous contribution is the displayed integral. Positivity of u gives gamma_delta>=0 and its stated integral. QED.

If each distribution is a measure with a bounded density near the selected point after removal of its atom, then A_N tends to c_N(a) and A_E tends to c_E(a), with an O(delta) error determined by those density bounds. Those separate regularity bounds are NOT established here. Without them, divergent or oscillatory contrasts may reveal more singular terms; a plateau on a few deltas is not an exact atom proof.

**Finite computation to run, not run here:** lambda=1, p=2, j=1, delta_l=min(1/64,a/16)*2^{-l}, l=0,1,2,3. Evaluate (24) by (7)--(11), with interval errors less than w_2/100, and the independent source calibration (25). Keep the coupled cross term rather than subtracting two uncontrolled large traces. Record three possibilities: contrast concentrated in N; in E; or shared/unresolved. Do not force the binary alternatives if both survive. The inverse-series degree is chosen from epsilon_d*m(z_+)+epsilon_d*m(z_-) and the stated absolute tolerance, not from a fit.

### 6.4 Contact and archimedean regular part

For u_delta with 2delta<log2 the prime contribution vanishes. Thus

\[
 [n_\lambda(u_\delta)-\mathcal D(u_\delta)]-e_\lambda(u_\delta)=-c_A.
\tag{27}
\]

This calibrates the contact in the fixed subtraction convention. It does not permit assuming that e_lambda(u_delta) tends to -ell: that assertion additionally requires the angle distribution to have no contact/singular contribution at 0.

To probe a regular point t0 away from 0 and prime powers, use the same contrast with shift t0; (25) holds without w. The combined regular density is exactly -a(|t0|). The separate regular parts can be reconstructed by these localized tests only with independent regularity/tail control. No claim that all of either piece is an ordinary kernel is made.

Q3 is therefore **COMPUTATION_SPECIFIED**, not a fabricated answer (i) or (ii). What has been computed exactly is the total singular dictionary, the cutoff contact, the first projection derivative, the convergent inverse evaluator and its calibrated local contrast. The assignment of individual prime atoms remains open.

## 7. First remaining inequalities and cheapest decisive check

For the original cutoff and the full class

\[
 C_L^{pn}=\{v\in C_c^\infty((-L/2,L/2);\mathbb C):A_+(v)=A_-(v)=0\},
 \quad \log2<L\le\log3,
\]

the first unresolved claim is the explicit weighted comparison (4), equivalently the upper-inverse bound in (9) or its limit on that class. The series inverse exists with a proved norm budget; the SIGN of its pairing with the arithmetic form is not supplied by that fact. No self-adjoint spectral order or table substitutes for it.

The cheapest immediate check on the already running table is (15), then the three exactly pole-null two-bump tests (14). No duplicate cell generation is requested. For a finite test packet, apply the full Hermitian matrix version (10); it checks combinations the diagonal table cannot see. The next additional computation, only after those consistency checks, is the calibrated prime contrast (25). A nonzero residual beyond its explicit error bound is an object/discretization failure before it is a mathematical sign result.

The new class (12) and the fixed-S obstruction in the parent are consistent: (12) chooses the cutoff AFTER fixing a finite packet; the parent fixes the projection while canonical cutoffs exhaust the radical. Interchanging those quantifiers would be the same error we are avoiding.

## 8. Frozen observer scores and new forecasts

The observer's parallel table was not read, awaited or reconstructed. No numerical experiment, eigenvalue calculation or quadrature was run. Only text/hash and document-validation operations were performed locally.

| Observer prediction | Frozen probability | Fate | Reason |
|---|---:|---|---|
| P_SIGN_HOLDS_ON_TABLE | 0.45 | PENDING | No table was supplied or inspected; (12) has different cutoff quantifiers. |
| P_MECHANISM_NAMED | 0.35 | CONFIRMED_FINITE_CLASS_ONLY | Equations (7)--(11) give a proved one-sided finite-packet certificate with an explicit inverse tail. No semilocal all-test spectral theorem is claimed. |
| P_R2_OBSTRUCTION_IS_RH | 0.60 | CONFIRMED_FOR_INCLUSION_ONLY_WITH_SCOPE_REPAIR | The comparison is the source's RH-linked condition, and (23) alone does not give its error. The stronger reading "nothing else is known in C99" is refuted by Lemma 3; that is not attributed to the narrower prediction. |
| P_PRIMES_IN_SONIN_TRACE | 0.40 | UNRESOLVED | Separate singular coefficients have not been proved; (25) is a specified discriminating computation, not its outcome. |

The following are new forecasts for the explicit tests above at lambda=1. They precede our access to the table, **not necessarily its generation**. They are subjective forecasts, not measured data or confidence in RH.

```yaml
BLIND_TO_PARALLEL_TABLE: true
PREDICTIONS_PRECEDE_TABLE_CREATION: not_claimed_parallel_run_already_reported
TABLE_CUTOFF: T_equals_W_equals_1
P_WIDE_BUMP_E_POSITIVE_FOR_B3_4_6:
  probability: 0.99
  tests: explicit_smoothed_cosine_v_b_of_section4
  event: E_gt_N_gt_0_at_b3_4_6
  mathematical_status: follows_from_equation17_for_exact_objects
  fate: PENDING_TABLE_VALIDATION
P_NARROW_SINGLE_BUMP_E_POSITIVE:
  probability: 0.65
  tests: normalized_eta_delta0_shifted_to_plus_and_minus_log2_over2
  event: E_positive_at_both_centers
  exact_guard: the_two_values_must_be_equal
  fate: PENDING
P_CANONICAL_CUTOFF_R1_E_POSITIVE:
  probability: 0.85
  test: explicit_quintic_mollified_chi_1_times_f0_in_section4
  fate: PENDING
P_CANONICAL_CUTOFF_R2_E_POSITIVE:
  probability: 0.90
  test: explicit_quintic_mollified_chi_2_times_f0_in_section4
  fate: PENDING
P_POLE_NULL_TWO_BUMP_FALSIFIER_RATIO:
  probability: 0.40
  test: v_plus_in_equation14
  event: 0_lt_E_over_N_lt_1_over4
  point_estimate: none
  fate: PENDING
P_FALSIFIER_RANKS_ABOVE_PHASE_CONTROLS:
  probability: 0.55
  event: E_over_N_for_v_plus_is_largest_among_v_plus_v_minus_v_i
  fate: PENDING
P_INVERSE_POLYNOMIAL_ENCLOSURE_SURVIVES_INDEPENDENT_CHECK:
  probability: 0.94
  event: equations6_through11_need_no_statement_weakening
  fate: PENDING
P_HIGH_MODULATION_LARGE_CUTOFF_PROOF_SURVIVES:
  probability: 0.85
  event: equation12_with_its_stated_quantifiers_survives_independent_check
  fate: PENDING
P_ATOM_CONTRAST_CALIBRATION_SURVIVES:
  probability: 0.93
  event: equations25_through27_have_the_stated_signs_and_factors
  fate: PENDING
```

Raw positive bumps and canonical cutoffs are NOT substituted for pole-null tests when scoring P_SIGN_HOLDS_ON_TABLE. Positions of a single translated bump cannot change its source sign. Different cutoff conventions or different bump definitions require separate events rather than retrospective reinterpretation.

## 9. Closeout

Q1 supplied an exact overlap criterion, a source-independent convergent inverse budget, a finite-space certificate, a nonempty adjustable-cutoff sign theorem and explicit falsifiers. It did not prove the full log-3 class at the reference cutoff. Q2 located the actual image-trace comparison, corrected its characteristic-zero implementation and recovered the extra harmonic-limit result already in the source. Q3 supplied a controlled finite evaluator and an atom/contact calibration; its requested individual atomic assignment is still unproved.

No target was rejected for implying RH. No new free positive floor or convergence hypothesis has been installed in a completed proof. The scalar source, pole, support and cutoff objects were kept distinct throughout.

Progress class: PROOF_PROGRESS for the inverse and restricted sign lemmas; SOURCE_CORRECTION for the prolate and 1999 citations; COMPUTATION_SPECIFIED for the atomic allocation. The main unresolved quantity is the sign of the explicit test-space matrix in (10) at the frozen cutoff and, independently, the local regularity needed to convert (24) into exact atom coefficients. Those are not declared closed by this document.

Only this verdict is authorized for repository write. No prior document, probability, state, queue, Lean source or numerical result is modified. Commit/blob/readback receipts are reported outside these immutable contents after the write.
