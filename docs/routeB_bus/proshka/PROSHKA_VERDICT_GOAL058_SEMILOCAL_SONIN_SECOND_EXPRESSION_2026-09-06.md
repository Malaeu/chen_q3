# STATUS: TRY_SEMILOCAL_SPLIT_WITH_FIXED_S_RADICAL_OBSTRUCTION
```yaml
PRIMARY: TRY_SEMILOCAL_SPLIT_WITH_FIXED_S_RADICAL_OBSTRUCTION
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_SEMILOCAL_SPLIT_WITH_FIXED_S_RADICAL_OBSTRUCTION
RESULT: SECOND_EXPRESSION_CANDIDATE
ANSWER: A_WITH_EXPLICIT_SCOPE_REPAIRS
RESULT_SCOPE: positive_semilocal_trace_minus_explicit_pair_data_remainder
GLOBAL_POSITIVITY_OR_RADICAL_FILTER_PASSED: false
REQUEST_ID: REQ-2026-09-06-SEMILOCAL
BOUNDARY_ID: GOAL058_SEMILOCAL_SONIN_SECOND_EXPRESSION
REQUEST_LOCK:
  COMMIT: c7d1320eef42a55a7159230c0cc96d9722046c85
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_SEMILOCAL_SONIN_SECOND_EXPRESSION_2026-09-06.txt
  GIT_BLOB: 011b259908a6abb734dcbf80e5fd94bee5795a6e
  SHA256: ee693f5ea54b176164125a1ff8712fb25c645fba4bb623e5d6b734508e044811
  BYTES: 12182
  LINES: 106
  FINAL_LF: true
  FETCHED_UTF8_REENCODING_HASHES_INDEPENDENTLY_RECOMPUTED: true
EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SEMILOCAL_SONIN_SECOND_EXPRESSION_2026-09-06.md
PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_SECOND_EXPRESSION
  SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
  TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false
DECISION:
  EXPLICIT_SEMILOCAL_PROJECTION_SPLIT: PRESERVED
  EXPLICIT_REMAINDER: pair_spectral_trace_distribution_with_cutoff_contact_term
  POINTWISE_EPSILON_SERIES_REGULARITY: NOT_ESTABLISHED
  SEMILOCAL_SONIN_DIMENSION: infinite
  FULL_PAIR_IN_GENERIC_POSITION: false_common_kernel_is_infinite_dimensional
  STRUCTURAL_GAIN_FROM_SPLITTING: true
  B_NO_GAIN_OR_TOO_SMALL_DIMENSION_ARGUMENT: REJECTED
  FIXED_S_BARE_TRACE_ANNIHILATES_GLOBAL_CANONICAL_RADICAL: false
  FIXED_S_BARE_TRACE_MINORISES_FULL_Q_ON_ALL_COMPACT_TESTS: false
  CUTOFF_IMAGE_ETA_S_ANNIHILATED: true
  CUTOFF_IMAGE_EQUALS_GLOBAL_E_IMAGE: false
  SEMILOCAL_TRACE_IDENTITY_22_REFUTED: false
  COFINAL_OR_DOMAIN_RESTRICTED_SEMILOCAL_ROUTE_REFUTED: false
  RH_EQUIVALENCE_USED_AS_A_KILL_REASON: false
NEW_PAPER_RESULTS:
  - compact_semilocal_truncated_Fourier_operator_from_finite_Euler_intertwiner
  - explicit_Sonin_orthogonal_projection_with_independent_positive_Gram_inverse
  - pair_angle_remainder_formula_in_the_published_trace_domain
  - two_sided_comparison_of_semilocal_and_archimedean_positive_trace_squares
  - strict_fixed_S_radical_cutoff_counterexample
  - explicit_negative_local_form_test_without_the_global_pole_term
  - exact_archimedean_constant_and_prime_shell_dictionary
CLOSES: [REQ-2026-09-06-SEMILOCAL]
CLOSES_ANALYTIC_RH_SUPPLIERS: []
OPENS: []
VERIFIER: PAPER
INDEPENDENT_KERNEL_VERIFICATION: false
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
NEGATION_OF_RH_CLAIM: false
```

## 0. Decision: a real splitting, but not the proposed global radical-annihilating factor

The semilocal splitting exists at the operator level, and its angle contribution has an explicit trace-distribution formula. Its positive term is genuinely prime-dependent. The semilocal Sonin space is infinite-dimensional. Calling all of this “no structural gain” or rejecting it because the eventual target implies RH would be wrong.

However, for each fixed finite S and fixed finite positive cutoffs, the bare positive Sonin trace cannot annihilate the full canonical radical in the project. More strongly, there are compact canonical cutoffs v_R for which

\[
\mathcal Q(v_R)-\|\vartheta(v_R)\mathsf S_S\|_{\rm HS}^2<0.
\tag{KILL}
\]

This is a strict analytic counterexample to the proposed unrestricted minorant, not to the trace formula, not to RH, and not to a construction whose set of places and projections vary cofinally. The selected answer is A: SECOND_EXPRESSION_CANDIDATE, because the explicit positive-minus-remainder splitting survives and provides structure. It has not passed the stronger global-radical filter. The counterexample refutes that upgrade, not the splitting that the task asks us to compute.

Two object corrections are essential. First, the local functional in (22) is missing the global pole term of the full Weil form. Second, Connes 1999's projection S_Lambda is a multiplicative-window projection, not the Sonin projection. Neither may be silently identified with the other object.

All proofs newly supplied here are PAPER derivations for independent checking. No claim of priority over the literature or Lean verification is made.

### Sources and page conventions

[C26] A. Connes, *The Riemann Hypothesis: Past, Present and a Letter Through Time*, arXiv:2602.04022v1. Printed pp.31–32: (19), Theorem 7.1, (20)–(22); endnote 11, p.36, (29)–(32). Use PDF numbering: the HTML renumbers these equations.

[CC20] A. Connes–C. Consani, *Weil positivity and Trace formula, the archimedean place*, arXiv:2006.13771, the 57-page source read in this audit. Printed pp.22–28: pair-of-projections calculation, especially Theorem 4.7, (83)–(84), p.27, and its proof p.28. Theorem 6.11, (141), p.48, retains support and transform-vanishing conditions. Sonin's infinite-dimensionality is stated on p.6.

[CCM23] A. Connes–C. Consani–H. Moscovici, *Zeta zeros and prolate wave operators: Semilocal adelic operators*, arXiv:2310.18423v1. Section 4.1, (35)–(42), pp.16–17; Proposition 4.1, (43)–(46), pp.17–18; Definition 4.10 and Proposition 4.11, pp.23–24; Proposition 4.12 and Theorem 4.13, pp.24–25. Theorem 4.13 gives a Hilbertian isomorphism, not an isometry. The introductory discussion pp.3–4 distinguishes the proposed prolate construction from an already completed operator/domain comparison.

[C99] A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta function*, arXiv:math/9811068v1. Theorem 4, p.31, is an asymptotic cutoff trace formula with o(1); its local principal values are normalized by the additive Fourier transform at 1. Section VIII, pp.42–43, (22)–(24), concerns the different global image and window projections. Appendix II, pp.71–72, fixes the unramified local normalization.

[CC21] A. Connes–C. Consani, *Spectral Triples and Zeta-Cycles*, arXiv:2106.01715v1, Proposition 2.1, (2.11), pp.4–5; Sections 2.2–2.3, pp.5–7. The window and perturbed-prime observations there are numerical experiments, not an exact positivity theorem beyond log 2.

[CCM07] A. Connes–C. Consani–M. Marcolli, arXiv:math/0703392, Section 2.3 and Section 7.2, for the correspondence analogy and the range of the global reduction map. A global reduction map is not replaced below by its finite-Euler analogue.

[Q] `paper_weil/sections/setup.tex`, blob `8637e3d973ba689c0cfd5d09a10e2dec3edd3caa`, at the request commit: the full complex form, its pole evaluations, the control-space norm and its continuity bound.

[F0] `paper_weil/sections/canonical.tex`, blob `fd0c7512e742f504fd3b64736aad5dbaec99ab1f`, at the request commit: f_0, its Fourier identity, cutoff convergence and radical inclusion. The displayed translates/convolutions are proved to be contained in the radical; the paper does not identify them as the entire radical.

[POLICY] `docs/WHY_NOT_YET.md`, blob `8e752c8c7e41efce99c2ec5dd69ce69704c6f140`, and the usage card in the request. Their classifications are claims to audit, not mathematical premises. No file in the shelf is edited.

The pinned request was fetched from GitHub, decoded as UTF-8 and re-encoded without normalization. Both independently computed hashes, size, line count and final LF agree. Later branch contents are not used as analytic suppliers.

## 1. 2(a): exact semilocal objects and two distinct Euler maps

Let \(S=\{\infty\}\cup S_f\), where S_f is finite and nonempty. Put

\[
\mathbb A_S=\mathbb R\times\prod_{p\in S_f}\mathbb Q_p,
\qquad
\Gamma_S=\{\pm\prod_{p\in S_f}p^{n_p}:n_p\in\mathbb Z\},
\]
\[
Y_S=\mathbb A_S/\Gamma_S,
\quad C_S=\mathbb A_S^\times/\Gamma_S,
\quad \operatorname{Mod}_S(x)=\prod_{v\in S}|x_v|_v.
\]

The product formula makes Mod_S invariant under Gamma_S. With
\(K_S=\ker(\operatorname{Mod}_S:C_S\to\mathbb R_+^*)\), one has
\(C_S\simeq\mathbb R_+^*\times K_S\), with K_S compact. Haar measure on K_S has mass one. The unitary w_S in [C26, endnote 11, (29)–(32)] identifies the K_S-invariant Hilbert space with \(L^2(\mathbb R_+^*,d^*u)\). We use the quotient Hilbert space and Fourier operator constructed in [CCM23], not a pointwise Fourier transform on arbitrary quotient representatives.

After x=log u the common model is \(\mathcal H=L^2(\mathbb R,dx)\). Scaling becomes translation

\[
(U_a v)(x)=v(x-a),\qquad
\vartheta(k)=\int_{\mathbb R_+^*}k(\rho)\vartheta(\rho)\,d^*\rho.
\]

For \(v(x)=k(e^x)\), the last operator is convolution by v. All tests may be complex. The physical evenness used to identify \(L^2(\mathbb R)^{ev}\) with the positive multiplicative line does not restrict log-coordinate v to be even.

Let \(P_T\) be multiplication by \(1_{x\le\log T}\) in the common model, and let \(\mathcal F_S\) denote the transported semilocal Fourier involution. Define

\[
Q_W=\mathcal F_S P_W\mathcal F_S,
\quad \mathsf S_S=(\operatorname{ran}P_T\vee\operatorname{ran}Q_W)^\perp
\quad\text{(orthogonal projection)}.
\]

The join means closed linear span. Simultaneous conjugation by a dilation reduces T,W to equal cutoffs \(\lambda=\sqrt{TW}\), because scaling expands the position cutoff and contracts the Fourier cutoff. The operator \(\vartheta(k)\) commutes with that conjugating dilation. The number \(\ell=\log(TW)\) is retained in the trace formula. We prove angle formulas at equal cutoffs, then transport back.

### Lemma 1 — explicit bounded Euler intertwiners [ABSTRACT][PAPER]

Write \(r_p=p^{-1/2}\), \(a_p=\log p\), and let \(M_S\) be the positive integers whose prime factors lie in S_f. Define

\[
J_S=\prod_{p\in S_f}(I-r_pU_{-a_p})^{-1}
=\sum_{n\in M_S}n^{-1/2}U_{-\log n},
\quad B_S=J_S^{-*}=\prod_{p\in S_f}(I-r_pU_{a_p}).
\tag{1}
\]

These are explicit bounded invertible operators. Put

\[
a_S=\prod_{p\in S_f}(1-r_p)>0,
\qquad b_S=\prod_{p\in S_f}(1+r_p).
\]

Then

\[
a_S\|v\|\le\|B_Sv\|\le b_S\|v\|.
\tag{2}
\]

In this model J_S represents \(\eta_S\), while B_S represents \(\theta_S\) of [CCM23, Propositions 4.1, 4.11–4.12]. These maps are not the scaling representation \(\vartheta\).

**Proof.** Each geometric operator series converges in norm since r_p<1. Finiteness of S_f gives norm convergence of their product and of the displayed M_S sum. The upper and lower bounds follow either factor by factor or by Fourier multiplication. With \(\widehat v(\tau)=\int v(x)e^{-i\tau x}dx\), the multipliers are respectively

\[
\prod_p(1-p^{-1/2+i\tau})^{-1},\qquad
\prod_p(1-p^{-1/2-i\tau}).
\]

They agree with the source formulas (43) and (57). On the multiplicative line, J_S corresponds to \(u^{1/2}\sum_{n\in M_S}f(nu)\); B_S for one prime is \(w_\infty f(u)-p^{-1/2}w_\infty f(u/p)\). This proves the dictionary. The source Fourier intertwining gives
\(\mathcal F_S J_S=J_S\mathcal F_\infty\) and
\(\mathcal F_S B_S=B_S\mathcal F_\infty\). □

The sum over M_S is not the global sum over every positive integer. This distinction is load-bearing in the radical question.

### Lemma 2 — position, compact angles and dimension [ABSTRACT][PAPER]

On the K_S-invariant space:

1. \(\operatorname{ran}P_\lambda\cap\operatorname{ran}Q_\lambda=\{0\}\).
2. \(P_\lambda\mathcal F_S P_\lambda\) is compact and self-adjoint on \(\operatorname{ran}P_\lambda\).
3. The common kernel of P_lambda and Q_lambda is infinite-dimensional.

Thus the full pair is **not** in generic position. Its nontrivial angle summands have the usual generic two-projection blocks; the common kernel must not be discarded.

**Proof.** J_S and J_S^{-1} preserve the subspace \(x\le\log\lambda\), and map it onto itself: each shift in their expressions is to the left. If h and \(\mathcal F_Sh\) lie in that subspace, then f=J_S^{-1}h and \(\mathcal F_\infty f=J_S^{-1}\mathcal F_Sh\) do too. In physical archimedean coordinates f and its Fourier transform would both have bounded support. The Fourier transform of a compactly supported L2 function is entire, hence it cannot vanish on an open real interval unless f=0. This proves (1).

For (2), expand J_S in its norm-convergent series in
\(P_\lambda J_S\mathcal F_\infty P_\lambda J_S^{-1}P_\lambda\).
Every \(P_\lambda U_{-\log n}\mathcal F_\infty P_\lambda\) is compact: in physical coordinates it is a truncated cosine-Fourier transform between two bounded intervals, up to a unitary dilation, with square-integrable kernel. Each term is therefore compact. Their norm-convergent sum is compact. Self-adjointness follows because \(\mathcal F_S\) is a self-adjoint involution.

For (3), [CCM23, Theorem 4.13, p.25] identifies the semilocal Sonin space with the infinite-dimensional archimedean Sonin space by the bounded invertible map B_S. The latter dimension is part of the Sonin theory used in [CC20, p.6]. □

No assertion about the dimensions of the two orthogonal-only intersections is needed; zero-angle summands are retained below. The compactness proof does not prove summability of all angle eigenvalues. Nor does [CCM23]'s proposed cyclic-pair prolate operator automatically supply a self-adjoint operator commuting with both literal cutoff projections: its needed domain/commutation theorem is not imported here.

## 2. 2(b): explicit splitting, with the missing contact term restored

Write \(P=P_\lambda\), \(Q=Q_\lambda\), \(\mathsf S=\mathsf S_S\), and

\[
D_S=P+Q-(I-\mathsf S).
\]

The bounded operator identity is

\[
\boxed{I-P-Q=\mathsf S-D_S.}
\tag{3}
\]

Let \(L_S(k)=-\sum_{v\in S}W_v(k)\). Importing the trace formula **as stated** in [C26, (22), p.32] gives

\[
\boxed{L_S(k)=N_S(k)-E_S(k),}
\tag{4}
\]
\[
N_S(k)=\operatorname{Tr}(\vartheta(k)\mathsf S),
\quad
E_S(k)=\operatorname{Tr}(\vartheta(k)D_S)-\ell k(1),
\quad\ell=\log(TW).
\tag{5}
\]

The term \(-\ell\delta_1\) belongs to E_S. Omitting it is an error unless TW=1 or k(1)=0. We do not obtain (22) by dropping the o(1) in [C99, Theorem 4, p.31]; the latter theorem is separately an asymptotic statement about \(\widehat P_\Lambda P_\Lambda\), not (3).

### Lemma 3 — the angle kernel [ABSTRACT][PAPER]

Choose real orthonormal eigenvectors \(\xi_n\) of the compact real operator \(P\mathcal F_SP\), with nonzero eigenvalues \(\alpha_n\). They satisfy \(|\alpha_n|<1\), by Lemma 2. Set

\[
s_n=\sqrt{1-\alpha_n^2},\qquad
\zeta_n=(\mathcal F_S\xi_n-\alpha_n\xi_n)/s_n.
\]

On the orthonormal pair (xi_n,zeta_n),

\[
P_n=\begin{pmatrix}1&0\\0&0\end{pmatrix},\quad
Q_n=\begin{pmatrix}\alpha_n^2&\alpha_ns_n\\
\alpha_ns_n&s_n^2\end{pmatrix},\quad
(D_S)_n=\begin{pmatrix}\alpha_n^2&\alpha_ns_n\\
\alpha_ns_n&-\alpha_n^2\end{pmatrix}.
\tag{6}
\]

The eigenvalues of D_S on that block are \(\pm|\alpha_n|\). Its value on the common kernel and on the zero-angle summands is zero. For A=theta(k), its block trace is exactly

\[
\alpha_n^2(\langle\xi_n,A\xi_n\rangle-\langle\zeta_n,A\zeta_n\rangle)
+\alpha_ns_n(\langle\xi_n,A\zeta_n\rangle+\langle\zeta_n,A\xi_n\rangle).
\tag{7}
\]

For a single dilation with rho>=1, (7) reduces to

\[
\epsilon_{S,n}(\rho)=
\frac{\alpha_n}{\sqrt{1-\alpha_n^2}}
\langle\xi_n,\vartheta(\rho^{-1})\zeta_n\rangle.
\tag{8}
\]

Extend it by \(\epsilon_{S,n}(\rho^{-1})=\epsilon_{S,n}(\rho)\). In the test-trace sense,

\[
\boxed{
E_S(k)=\left\langle\sum_n\epsilon_{S,n}-\ell\delta_1,
                  k(\rho^{-1})\right\rangle.}
\tag{9}
\]

**Proof.** The projection identities and Fourier involution give the matrices (6). On this block \(\mathcal F_S\) has matrix \(\left(\begin{smallmatrix}\alpha&s\\s&-\alpha\end{smallmatrix}\right)\). For a real dilation operator A=theta(rho^{-1}), Fourier covariance \(\mathcal F_S\vartheta(\rho)\mathcal F_S=\vartheta(\rho^{-1})\), and realness of xi,zeta, imply

\[
\langle\xi,A\xi\rangle-\langle\zeta,A\zeta\rangle
=\frac\alpha s(\langle\xi,A\zeta\rangle+\langle\zeta,A\xi\rangle).
\]

To check it, expand the diagonal matrix coefficient of A between \(\mathcal F_S\xi=\alpha\xi+s\zeta\), replace A by its inverse by covariance, and use \(\langle v,A^{-1}v\rangle=\langle v,Av\rangle\) for real v. Substitution into (7) leaves \(\alpha/s\) times the cross-sum. For rho>=1, theta(rho^{-1})xi is still supported inside the cutoff, while zeta is outside, so \(\langle\zeta,\vartheta(\rho^{-1})\xi\rangle=0\). This proves (8), and the cross-sum is invariant under rho->rho^{-1}. Integration gives (9). These are precisely the algebra and support steps of [CC20, (82), (87)–(89), pp.27–28], here supplied for the semilocal pair. □

**Trace and convergence scope.** Equations (4)–(9) use the smooth test domain and the trace interpretation of the imported (22). In an ordinary trace-class realization, if \(\vartheta(k)(I-P-Q)\) is trace class, then multiplying on the right by \(\mathsf S\) or \(I-\mathsf S\) proves trace class of the two pieces. The sums of integrated block traces are then absolutely convergent in an eigenbasis of D_S. This justifies the weak series, not an interchange of an unproved pointwise series with every integral. If a realization uses regularized traces, (4) must instead use that same regularization; cyclicity cannot be borrowed from ordinary trace class without proof.

No new semilocal proof of locally uniform or absolute pointwise convergence of \(\sum\epsilon_{S,n}(\rho)\) is supplied. Consequently the unconditional object established here from the published test trace is an explicit **trace distribution**. It is not asserted to have all the function-level regularity of the archimedean (84). Neither is a theorem of nonexistence of such a function claimed. The two function-level alternatives in the question do not exhaust this intermediate possibility.

### Exact Halmos plant

For \(\alpha=3/5\), \(s=4/5\), and \(v=(2,1)/\sqrt5\), the matrices (6) give

\[
\langle v,(I-P-Q)v\rangle=-3/5,
\qquad \mathsf S v=0.
\tag{10}
\]

Thus \(I-P-Q\not\succeq0\), and it cannot be bounded below by a positive multiple of the Sonin projection on every direction. This does not prove that the arithmetic convolution-square trace must be negative on its admissible restricted domain. The exact class of operators \(\vartheta(k*k^*)\) remains relevant. Infinite-dimensional Sonin space is not “too small by dimension count.”

## 3. A source-defined positive projection and its prime dependence

The statement that a Hilbertian isomorphism preserves the norm would be false. We instead compute the needed correction explicitly.

### Lemma 4 — corrected Sonin projector [ABSTRACT][PAPER]

Let \(\mathsf S_\infty\) denote the archimedean Sonin projection at lambda, and use B_S from (1). On \(\mathcal H_0=\operatorname{ran}\mathsf S_\infty\), define

\[
G_S=\mathsf S_\infty B_S^*B_S\mathsf S_\infty|_{\mathcal H_0}.
\]

Then

\[
a_S^2I\le G_S\le b_S^2I,
\qquad
\boxed{\mathsf S_S=B_S\mathsf S_\infty G_S^{-1}
                      \mathsf S_\infty B_S^*.}
\tag{11}
\]

For a compact smooth multiplicative test k put

\[
\mathcal N_S(k)=\|\vartheta(k)\mathsf S_S\|_{\rm HS}^2
=\operatorname{Tr}(\vartheta(k)\mathsf S_S\vartheta(k)^*)\ge0.
\]

One has the explicit comparison

\[
\boxed{
\left(\frac{a_S}{b_S}\right)^2\mathcal N_\infty(k)
\le \mathcal N_S(k)
\le\left(\frac{b_S}{a_S}\right)^2\mathcal N_\infty(k).}
\tag{12}
\]

In particular, these Hilbert–Schmidt squares are finite on this test class.

**Proof.** The source theorem [CCM23, Theorem 4.13] says that the semilocal Sonin space is B_S(H_0). The bounds (2) yield the bounds on G_S, with no Weil positivity assumption. The map
\(W=B_S|_{H_0}G_S^{-1/2}\) is an isometry onto that range. Its orthogonal range projection WW* is (11). The Hilbert–Schmidt norm in question equals \(\|\vartheta(k)W\|_{\rm HS}\). Convolution theta(k) commutes with B_S, since both are translation multipliers. Multiplication on the left by B_S and on the right by G_S^{-1/2}, with the two independent norm bounds, gives (12). Finiteness of the archimedean square follows from [CC20, Theorem 4.7] on compact smooth tests, transported by dilation for general lambda. □

This is constructive structure: the inverse in (11) has an independently proved bound \(a_S^{-2}\), not a lower bound on the unknown Weil form.

### 2(c): exact prime contribution and what its allocation does not say

The normalization of [C99, Theorem 4 and Appendix II] gives, after passing from its unnormalized scaling U to unitary theta,

\[
\boxed{
W_p(k)=\log p\sum_{j\ge1}p^{-j/2}
                   \bigl(k(p^j)+k(p^{-j})\bigr).}
\tag{13}
\]

For compact k this is a finite sum. Here the multiplicative Haar measure has mass log p per valuation shell. To verify both coefficients, put \(h(\rho)=\rho^{-1/2}k(\rho)\), so theta(k)=U(h). In the local integral \(h(u^{-1})/|1-u|_p\), the shell \(|u|_p=p^{-j}\) has denominator 1 and the shell \(|u|_p=p^j\) has denominator p^j. Both leave the factor p^{-j/2}; they evaluate k at p^j and p^{-j}. The unramified unit contribution is fixed by the principal-value normalization (additive Fourier transform vanishing at 1), not by a freely chosen extra delta constant.

The prime data enter **both** constructed pieces: B_S and G_S in the positive projector (11), and alpha_n,xi_n,zeta_n in (9). Therefore the slogan “the positive piece is archimedean and every prime must be entirely in epsilon” is not a deduction from Sonin-space stability.

A stronger assertion assigning each distributional atom of (13) exclusively to N_S or E_S would require computing their singular parts separately. That computation has not been done here. Nonnegativity of \(\mathcal N_S\), or explicit prime dependence of (11), does not establish individual atomic coefficients. What is proved is the total difference (4) with the exact arithmetic coefficients (13). The registered prime-allocation prediction is therefore not credited as proved.

## 4. 2(f): the full Weil form, the pole correction and c_A

Let \(v\in C_c^\infty(\mathbb R;\mathbb C)\), \(k(u)=v(\log u)\), and \(f=k*k^*\). Then

\[
f(1)=\|v\|_2^2,
\quad f(p^j)+f(p^{-j})=2C_v(j\log p),
\quad C_v(t)=\Re\int\overline{v(x)}v(x+t)dx.
\]

In the conventions [Q], [CC21, Proposition 2.1, (2.11)] and [CC20],

\[
L_S(f)=\mathcal D(v)-c_A\|v\|_2^2
 -2\sum_{p\in S_f,j\ge1}\frac{\log p}{p^{j/2}}C_v(j\log p),
\tag{14}
\]
\[
a(t)=\frac{e^{-t/2}}{1-e^{-2t}},\qquad
\mathcal D(v)=\int_0^\infty a(t)\|v(\cdot+t)-v\|_2^2dt.
\]

The full source form is

\[
\boxed{
\mathcal Q(v)=L_S(f)+P_{02}(v)
 -2\sum_{p\notin S_f,j\ge1}\frac{\log p}{p^{j/2}}C_v(j\log p),}
\tag{15}
\]
\[
P_{02}(v)=2\Re\bigl(A_+(v)\overline{A_-(v)}\bigr),
\qquad A_\pm(v)=\int v(x)e^{\pm x/2}dx.
\]

If the support diameter is at most L and S_f contains every prime <=e^L, the last sum vanishes. Even then, \(\mathcal Q=L_S\) requires the pole term to vanish. That is a test-class condition, not a property of every complex test. On the canonical noncompact vector, \(A_\pm(f_0)=1/(2A)\ne0\), since \(\widehat f_0=\Xi/A\) and \(\xi(0)=\xi(1)=1/2\). The value \(A\approx0.565466013092\) is an approximation to a defined norm, not its exact definition.

### Lemma 5 — exact constant [ABSTRACT][PAPER]

The archimedean contact constant is

\[
\boxed{c_A=\gamma_E+\log(8\pi)+\pi/2.}
\tag{16}
\]

It is obtained without fitting and independently of S_f. Starting with \(c_0=\gamma_E+\log(4\pi)\), the conversion to difference energy adds twice

\[
I=\int_0^\infty(1-e^{-t/2})a(t)dt
=2\int_0^1\frac{du}{(1+u)(1+u^2)}
=\tfrac12\log2+\tfrac\pi4.
\]

Thus c_A=c_0+2I. The substitution is u=e^{-t/2}; partial fractions evaluate the elementary integral. This also agrees with
\(\psi(1/4)=-\gamma_E-\pi/2-3\log2\) and the archimedean multiplier
\(\Re\psi(1/4+i\tau/2)-\log\pi\) in [Q]. □

The term log(TW) is a cutoff contact term in (5), not the origin of the gamma constant. At TW=1 it is zero and c_A is unchanged. The CC20 constant \(4\gamma/\log2\) in Theorem 6.11 controls a different remainder; its gamma is not Euler's constant. Their inequality does not fail normalization merely because that constant differs from c_A.

### Lemma 6 — genuine finite-S negative local-form plant [COFINAL_FAMILY][PAPER]

For each fixed finite S, the local functional L_S is **not** nonnegative on all compact convolution squares. Let h be any nonnegative smooth compact function with \(\|h\|_2=1\), and let \(v_b(x)=b^{-1/2}h(x/b)\). Then

\[
\boxed{L_S(k_b*k_b^*)\le -c_A+18\|h'\|_2^2/b^2.}
\tag{17}
\]

Consequently it is at most \(-c_A/2\) if \(b^2\ge36\|h'\|_2^2/c_A\).

**Proof.** Nonnegativity of h gives \(C_{v_b}(t)\ge0\), so every prime term in (14) is nonpositive. Moreover
\(\|v_b(\cdot+t)-v_b\|_2\le |t|\|h'\|_2/b\).
Expanding a(t) into positive exponentials and applying Tonelli,

\[
\int_0^\infty t^2a(t)dt
=2\sum_{j\ge0}(2j+1/2)^{-3}\le18.
\]

The last bound is the first term plus the integral bound for the decreasing tail. Insert it into (14). □

This is a plant with the genuine semilocal space and genuine primes. It is not an RH counterexample: it omits P_02. It shows why the unqualified residual inequality \(E_S(f)\le N_S(f)\) on **all** compact tests is actually false, not just an RH-equivalent coordinate.

## 5. 2(e): radical audit and the strict fixed-S obstruction

Three different statements were merged in the request. They must be separated.

### Lemma 7 — finite-Euler cutoff image [ABSTRACT][PAPER]

If the archimedean vector f is supported in the position cutoff, then

\[
\eta_S f\in\operatorname{ran}P_\lambda^S,
\qquad \mathsf S_S\eta_S f=0.
\tag{18}
\]

This is [CCM23, Proposition 4.1(iv)] and also follows from (1). No simultaneous Fourier support assumption is needed. If an archimedean L2 vector f and its Fourier transform are both supported in bounded cutoffs, then f=0 by the argument in Lemma 2. The version with both such supports is therefore vacuous in this archimedean input class.

This does not say that \(\mathsf S_S\) kills the global \(E(f)(u)=u^{1/2}\sum_{n\ge1}f(nu)\). In the finite-Euler image the sum ranges over M_S. For example, on a small positive bump and a suitable u, a term at an integer outside M_S is present in the global sum and absent in the semilocal sum. They cannot be identified by notation.

In [C99, Section VIII, pp.42–43], the inclusion \(Q'_{\Lambda,0}\le S_\Lambda\) concerns the range of a **global** reduction map inside a **multiplicative-window** subspace of \(L^2(C_k)\). It does not identify either of those projections with \(\mathsf S_S\). Its source class on the full adele space is not replaced here by an archimedean function compactly supported with compactly supported Fourier transform. The relation to trivial correspondences in [CCM07, Section 7.2] likewise supplies no equality of these Hilbert-space objects.

### Lemma 8 — no nonzero bounded L2 projection kills all canonical translates [ABSTRACT][PAPER]

The span of \(\{U_qf_0:q\in\mathbb R\}\) is dense in the unweighted logarithmic \(L^2(\mathbb R)\). Hence

\[
\bigl(\forall q:\ \mathsf S_S U_qf_0=0\bigr)
\quad\Longrightarrow\quad \mathsf S_S=0,
\tag{19}
\]

which contradicts Lemma 2.

**Proof.** By [F0], f_0 is in L1 and L2 and \(\widehat f_0=\Xi/A\). Since Xi is entire and not identically zero, its real zeros form a measure-zero discrete set; no RH assumption enters. If h is orthogonal to every translate, the L1 function \(\overline{\widehat h}\widehat f_0\) has Fourier transform zero everywhere. Uniqueness for the Fourier transform of an L1 function implies that this product is zero almost everywhere. Thus h=0. This proves density and (19). □

There is no contradiction with the radical of the project's form: that radical is closed in the stronger control-space topology X, not necessarily in the unweighted L2 topology. An unbounded or differently topologized factor is not ruled out by (19).

### Lemma 9 — strict compact-test counterexample to the bare trace minorant [COFINAL_FAMILY][PAPER]

Fix S,T,W. Let \(\mathsf S=\mathsf S_S\) and choose any unit vector h in its nonzero range. Define

\[
\epsilon_h=\|\vartheta(f_0)h\|_2^2
=\frac1{2\pi A^2}\int_{\mathbb R}
        |\Xi(\tau)|^2|\widehat h(\tau)|^2d\tau>0.
\tag{20}
\]

The expression \(\vartheta(f_0)\) here is the bounded convolution operator by the log function f_0. Let \(v_R=\chi_R f_0\) be the smooth compact canonical cutoffs from [F0], and let \(k_R(e^x)=v_R(x)\). For all sufficiently large R,

\[
\boxed{
\mathcal Q(v_R)-\mathcal N_S(k_R)\le-\epsilon_h/8<0.}
\tag{21}
\]

In particular, \(\mathcal Q(v)=\mathcal N_S(k)\) and even \(\mathcal Q(v)\ge\mathcal N_S(k)\) cannot hold for every complex compact smooth v with this fixed nonzero Sonin projection.

**Proof.** Convolution by f_0 is bounded because f_0 is in L1. Its Fourier multiplier is nonzero almost everywhere, so it is injective on L2, proving epsilon_h>0. Since \(\|v_R-f_0\|_1\to0\), Young's inequality gives
\(\|\vartheta(k_R)h-\vartheta(f_0)h\|_2\to0\).
Choose R large enough that this difference is at most \(\sqrt{\epsilon_h}/2\). Because Sh=h,

\[
\mathcal N_S(k_R)=\|\vartheta(k_R)\mathsf S\|_{\rm HS}^2
\ge\|\vartheta(k_R)h\|_2^2\ge\epsilon_h/4.
\]

On the other hand, f_0 is in the radical of the continuous form on X, and \(v_R-f_0\to0\) in X by [F0]. With the bound in [Q],

\[
|\mathcal Q(v_R)|
=|\mathcal Q(v_R-f_0)|
\le C_X\|v_R-f_0\|_X^2\to0.
\]

Choose the same R large enough that the last bound is at most epsilon_h/8. Subtraction proves (21). For an explicit cutoff budget, let a=pi/2 and use the normalized envelope constants M_0,M_1 and cutoff derivative bound 2 from [F0]. Put

\[
C_{\rm cut}=a^{-1}(17M_0^2/2+2M_1^2/3).
\]

The source cutoff estimates give
\(\|v_R-f_0\|_1\le(M_0/a)e^{-ae^{2R}}\) and
\(\|v_R-f_0\|_X^2\le C_{\rm cut}e^{-2ae^{2R}}\).
Thus any R>=0 satisfying

\[
(M_0/a)e^{-ae^{2R}}\le\sqrt{\epsilon_h}/2,
\qquad C_XC_{\rm cut}e^{-2ae^{2R}}\le\epsilon_h/8
\]

is a sufficient threshold. These are defined constants and a positive integral (20), not a fitted rate. □

This is an exact existence-and-budget counterexample, with no fitted numerical threshold. One may specify h as the normalization of B_S h_infty for any chosen nonzero archimedean Sonin vector h_infty, using Theorem 4.13. The same argument works with translated f_0 and with any nonzero f_0*h_c, h_c compact smooth: the corresponding multiplier is again nonzero almost everywhere.

**Scope that must not be lost:** S,T,W are fixed while R tends to infinity. This proof does not cover a diagonal in which S and the cutoffs also vary and h varies with them. The constants in (2)/(12) can deteriorate with S. Nor does it refute a trace corrected by E_S and the pole functional, an unbounded factor on a different completion, or the global window-minus-image construction in [C99]. The semilocal program itself remains available.

## 6. 2(d): plants that actually distinguish the source

### (i) Replacing Lambda(n) by 1

An abstract multiplicative group can still be written down after changing a weight. What fails is the equality between that altered arithmetic functional and the trace arising from the specified local fields, self-dual characters and Haar measures. Keeping those fixed, the shell computation (13) still gives log p at p^j and zero at non-prime-power integers. A test supported near a selected prime power separates the two distributions.

Thus refusing the altered weight is a **source-identity test**, not by itself a proof that the positive-trace method detects every negative direction. The nontrivial positivity plants here are (10), (17) and (21). Also distinguish Lambda(n)=1 from the previously refuted smooth measure substitution d psi=dx: these are different modified arithmetic distributions, not the same plant.

### (ii) Perturbing p to p(1+10^-3)

For the unchanged local field Q_p, the residue cardinality and valuation shells are still powers of p. Shifting one such frequency while retaining Q_p breaks (13), and therefore the intended source version of (22). A cyclic group generated by a perturbed real number certainly exists, but it is not the stated adelic quotient with that local Fourier theory. If the perturbed value is rational, its actual prime factorization produces a different set of places and different shell data, not a continuously adjustable one-prime field.

The numerical sensitivity in [CC21, Section 2.3] is not imported as a theorem of positivity or its failure for this particular perturbation. The exact conclusion here is the source mismatch.

### (iii) A genuine space with a deliberately false Euler factor

Keep the same semilocal Hilbert space and projections. At an existing prime p multiply the usual local factor by

\[
M_p(s)=(1-p^{a-s})(1-p^{a-1+s}),\qquad a=3/4.
\tag{22}
\]

This nonzero entire multiplier has explicit off-line zeros, and \(M_p(1-s)=M_p(s)\). For \(\Re s>3/4\),

\[
\boxed{
\frac{M_p'(s)}{M_p(s)}
=\log p+\log p\sum_{j\ge1}
          (p^{ja}+p^{j(1-a)})p^{-js}.}
\tag{23}
\]

**Proof.** Factor
\(M_p(s)=-p^{a-1+s}(1-p^{a-s})(1-p^{1-a-s})\)
and differentiate its logarithm in the indicated zero-free half-plane, using two absolutely convergent geometric series. Its zeros include \(s=a+2\pi i k/\log p\) and \(s=1-a+2\pi i k/\log p\). □

The new centered local-frequency coefficients include
\(2\log p\cosh((a-1/2)j\log p)\), together with the contact term. These are not the fixed Tate shell coefficients (13). The Hilbert-space pair and its split remain unchanged, whereas the putative arithmetic left side changes. Thus its analogue of (22) already fails at the local factor/trace identification; the positive trace cannot certify it. A test concentrated near p and avoiding 1 and the other relevant powers detects a changed coefficient exactly.

This is a legitimate false-factor plant on an existing space, not a claim that the modified factor is the local zeta factor of Q_p. No such freedom exists with the original local field, additive character and unitary scaling fixed. An ordinary reciprocal factor \((1-\chi(p)p^{-s})^{-1}\) itself has poles rather than zeros; for |chi(p)|=1 it does not create the requested off-line zeros. That example in the request needs this correction.

## 7. Yoshida window: what the splitting does and does not prove

For a support-matched S and a pole-null test, (4) gives

\[
\mathcal Q(v)=\mathcal N_S(k)-E_S(k*k^*).
\]

The CC-type lower bound \(\mathcal Q(v)\ge\mathcal N_S(k)\) would follow from the concrete inequality

\[
\boxed{E_S(k*k^*)\le0}
\tag{24}
\]

on the exact support and moment-constrained class. Mere nonnegativity of Q needs only \(E_S\le\mathcal N_S\), a different condition. If pole evaluations are retained, (24) is replaced by \(E_S\le P_{02}(v)\), after all active primes are included.

The present pair computation gives no sign in (24): its blocks have both signs (6), and the positive Gram inverse in (11) does not estimate their integrated signed combination. This is the precise missing estimate, expressed in explicit source data, not a new hypothesis being passed off as a theorem. A proof of it on a larger support class would be a genuine result; it is not rejected for being useful to RH.

No unconditional Thm-7.1-type inequality on a window strictly past L=log2 for S={infinity,2} is proved here. [CC20, Theorem 1/6.11] retains its given support and transform conditions. [CC21, Sections 2.2–2.3] reports numerical window experiments, not a sharp theorem that log2 is an absolute barrier. Therefore neither a larger-window theorem nor an impossibility theorem follows from the cited pages alone. This verdict does not reinstate an archimedean-only argument on a prime-active support.

The full bare fixed-S extension to *all* tests is genuinely false by (17)/(21). The limited larger-window, correctly conditioned problem is a different question and remains open in this attempt.

## 8. The owner's methodological objection and the historical analogy

**An implication to RH is not a defect in a proposed proof.** It is the required conclusion. Circularity is using an unproved RH-equivalent statement as a premise of that same proof. An independently derived equality or sharp inequality is entirely admissible. Logical equivalence does not make two representations equally accessible to a particular proof method; it is not a theorem about proof length or search cost.

Accordingly, the blanket rule in [POLICY, Section 4.1] that an RH-equivalent target is automatically filed away without investigation is not mathematically justified. The claim that only identities, never sharp inequalities, can reach a zero-margin problem is also not a theorem. These observations revise the evaluation of the policy, not the repository policy file itself, which this task does not authorize us to edit.

This batch does not discard a “new coordinate.” It supplies an explicit pair-spectrum expression (9), an independently norm-controlled projection (11), and then tests the stronger assertion about the full radical. The strict contradiction (21), not RH-equivalence, is the reason for the scoped rejection of the bare fixed-S factor. The overall splitting is retained as a second-expression candidate, not discarded.

Nor was Weil the only mathematician to obtain such finite-field results. Hasse's elliptic-function-field result predates Weil's general-curve theorem: H. Hasse, *Zur Theorie der abstrakten elliptischen Funktionenkörper III. Die Struktur des Meromorphismenrings. Die Riemannsche Vermutung*, J. reine angew. Math. 175 (1936), 193–208, DOI 10.1515/crll.1936.175.193. Deligne proved the higher-dimensional Weil conjecture: P. Deligne, *La conjecture de Weil I*, Publ. Math. IHES 43 (1974), 273–307, DOI 10.1007/BF02684373. These are independent primary references, not claims about the current source paper.

For the curve analogy, [CCM07, Section 2.3] describes the arithmetic/geometric comparison. The Hodge-index statement has an essential sign and a restricted domain: after removing the degree directions, the appropriate intersection form is negative, so its negative supplies the useful positive form. It is not a universal positive intersection form. The lesson is **a new, independently proved sign structure plus an exact comparison**, not that only a literal norm-square identity or only Weil's particular construction could ever work.

## 9. Prediction scoring, with original probabilities retained

| Registered event | p | Fate | Exact scope |
|---|---:|---|---|
| P_SPLIT_EXISTS | 0.55 | CONFIRMED_IN_TRACE_DISTRIBUTION_FORM | (3)–(9) give the explicit pair-data remainder; convergence as an ordinary pointwise epsilon function is not established. |
| P_PRIMES_IN_REMAINDER | 0.70 | NOT_ESTABLISHED | Both parts depend on the primes. An exclusive allocation of singular atomic coefficients has not been computed. |
| P_POSITIVITY_PAST_LOG2_BY_HAND | 0.20 | NOT_ESTABLISHED_IN_THIS_BATCH | No claimed larger-window theorem; this is not a proof of impossibility. |
| P_COORDINATE_AGAIN | 0.35 | REFUTED_AS_THE_PROPOSED_CLASSIFICATION | There is structural gain and Sonin is infinite-dimensional. Negative blocks exist, but the stated no-gain/dimension conclusion does not follow. The chosen result is A; the counterexample only excludes its unrestricted fixed-S upgrade. |
| P_RADICAL_KILLED_BY_SONIN | 0.60 | AMBIGUOUS_OBJECT_AS_REGISTERED | True for the finite-Euler position-cutoff image (18); the simultaneous archimedean upper-cutoff class is zero. False for the advertised global family by (19)–(21). These are not scored as one identical event. |
| P_CONSTANT_MATCHES | 0.65 | CONFIRMED_WITH_DICTIONARY | (16) recovers c_A exactly. The cutoff log contact and the global pole term remain separate. |

No probability is replaced. Neither absence of a proof nor failure on a different domain is relabeled a mathematical refutation of the frozen event.

Before an independent check of these new derivations, register:

```yaml
P_SEMILOCAL_FIXED_S_RADICAL_WITNESS:
  probability: 0.98
  event: equations_20_21_hold_in_the_common_log_Hilbert_model_without_RH
  fate: PENDING
P_SEMILOCAL_EULER_PROJECTOR_AND_COMPACT_ANGLE:
  probability: 0.80
  event: Lemmas_1_2_4_survive_independent_check_with_no_change_of_domain
  fate: PENDING
P_SEMILOCAL_ANGLE_TRACE_NORMALIZATION:
  probability: 0.84
  event: equations_8_9_13_16_survive_independent_sign_and_contact_term_check
  fate: PENDING
```

## 10. Cheapest decisive check and one bounded directive

The cheapest falsifier requires no eigenvalue calculation: verify (10) with the exact rational projections and verify the Young/Plancherel proof (20)–(21). These decide the unrestricted positivity and radical claims before any new semilocal numerical machinery.

For a computation on the finite shelf, first require an actual finite representation of **both source cutoff projections on one carrier**, together with a certified approximation to a nonzero Sonin vector and its tail error. A finite CCM Weil matrix is not itself this projection pair. If that data are absent, report `NO_SOURCE_LOCKED_FINITE_SONIN_PAIR`; do not substitute a ground vector from a different matrix.

If such data exist, the decisive functional is

\[
D_R=\mathcal Q(v_R)-\|\vartheta(k_R)h\|_2^2,
\quad \|h\|=1,\quad h\in\operatorname{ran}\mathsf S_S.
\]

Use a certified upper bound for Q and a certified lower bound for the norm, including the error in Sonin membership. A strict upper bound U(D_R)<0 refutes only the fixed-S global minorant. Lower-bound failure is not a negative certificate; a zero-consistent interval is inconclusive. The analytic target supplied by (21) is U(D_R)<=-epsilon_h/8 after the explicit L1 and X errors are below their indicated thresholds. No new numerical run was performed or authorized by this verdict.

**One bounded directive:** independently check the finite-Euler maps (1), the common-Hilbert-space dictionary, and the fixed-S counterexample (21) against the pinned sources. Retain (9)/(11) as the explicit semilocal split, but do not advertise its positive term alone as the global radical-annihilating second expression. Do not alter the paper, Lean, prior verdicts, queue or shared state.

## 11. What survives for constructive work

**R1 — joint corrected semilocal expression.** Keep the exact positive N_S, the signed angle distribution E_S, the global pole term and a support-matched set S together. The new task would be to prove (24), or its pole-retaining version, directly on a declared class. The sign is not supplied by Halmos theory alone. This retains the source arithmetic and is not ruled out by the fixed-S global witness. Estimated discriminating value 9/10; cost 8/10. These are planning judgments, not measured probabilities.

**R2 — varying global window-minus-image projections.** The exact inclusion in [C99, (23)] yields a positive difference of projections on a different space. Its independent trace-limit comparison is not proved here. It is not refuted by a theorem in which S and the positive projection are fixed. Restoring that distinction avoids killing a potentially useful construction because it shares a positivity target. Estimated discriminating value 9/10; cost 9/10.

No route is declared the fastest from an untested scalar comparison. Neither representation is entered as a closed supplier. A sufficient independent inequality can be pursued even when its conclusion would be RH.

### Closeout

- **Computed:** the explicit finite-Euler intertwiners, orthogonal Sonin projection, compact angle blocks, integrated epsilon distribution, and exact arithmetic normalization.
- **Refuted:** the bare fixed-S Sonin trace as an unrestricted lower bound for the full Weil form; its annihilation of the full global canonical radical; unqualified positivity of the local part without poles.
- **Not refuted:** the imported semilocal trace formula, source-restricted Sonin estimates, or a cofinal/global second-expression program.
- **Still not computed:** a separate allocation of prime atoms between the two trace distributions, pointwise semilocal epsilon regularity, and a larger-window signed-error bound.
- **Must not recur:** conflating the 1999 window projection with Sonin, the finite-Euler image with global E, or local L_S with full Q; killing a proof target merely because it implies RH.
- **Repository action:** one verdict at EXPECTED_VERDICT_PATH only. The commit identifier and readback digest are returned in a separate receipt after writing. Successful storage does not promote PAPER to LEAN.
