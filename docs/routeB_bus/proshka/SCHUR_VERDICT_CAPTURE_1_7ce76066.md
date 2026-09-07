# STATUS: TRY_DYADIC_POSITIVE_PRINCIPAL_KERNEL_AND_RELATIVE_SCHUR
```yaml
OPERATIVE_CLASS: TRY_DYADIC_POSITIVE_PRINCIPAL_KERNEL_AND_RELATIVE_SCHUR
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-07-SCHUR
BOUNDARY_ID: GOAL058_SIGNED_COMPLEMENT_FOR_THE_MOMENT_NULL_CLASS
RESULT:
  Q1: PARTIAL_WITH_PRECISE_REMAINDER
  Q1_HIGH_MODULATION: PROVED_ON_CLASS
  Q1_SECOND_DIFFERENCE_FAMILY: PROVED_ON_CLASS
  Q2: PROVED_ON_CLASS
  Q3: PARTIAL_WITH_PRECISE_REMAINDER
  Q4: PROVED_ON_CLASS
REQUEST_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  COMMIT: f859216e496f54115d4f9b81f8dc78881f2a8e7f
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_SIGNED_SCHUR_COMPLEMENT_2026-09-07.txt
  GIT_BLOB: 98d9f61f5cdfdae7ee4657114b2796f5eac6c175
  SHA256: 037bbaac38aeb577b68fe973b55ae905c3b88905d30bb06807d57c0c4c507e06
  BYTES: 15507
  LINES: 113
  FINAL_LF: true
  CONNECTOR_FETCH: true
  FETCHED_UTF8_REENCODING_HASHES_AND_COUNTS: ALL_MATCH
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
DECISIONS:
  WHOLE_CLASS_SCALAR_POSITIVITY: NOT_PROVED
  WHOLE_CLASS_FULL_MARGIN_POSITIVITY: NOT_PROVED
  SOURCE_NEGATIVE_DIRECTION: NOT_PRODUCED
  SIGNED_SCHUR_COMPLEMENT_NONNEGATIVE: NOT_PROVED
  WHOLE_CLASS_SUM_OF_SQUARES: NOT_CONSTRUCTED
  SOURCE_POSITIVE_PRINCIPAL_KERNEL: PAPER_PROVED_HERE
  REMAINDER_RELATIVELY_COMPACT_IN_PRINCIPAL_ENERGY: PAPER_PROVED_HERE
  NEGATIVE_INERTIA_OF_THIS_FIXED_CLASS_OPERATOR: FINITE_BY_NEW_PAPER_DERIVATION
  HIGH_MODULATION_SCALAR_FLOOR: EVENTUALLY_STRICTLY_POSITIVE
  HIGH_MODULATION_LEADING_COEFFICIENT: LOG_PERIODIC_NOT_A_SINGLE_CONSTANT
  SHIFTED_EULER_TRACE_NORM_EXPONENT: 3
  PINCHING_ASSUMPTION: ORTHOGONAL_PROJECTIONS_OR_STRONG_STAR_CONVERGENCE
  SINGULAR_VALUE_UPPER_RATE: O_N_INVERSE
  EXACT_WEYL_EQUIVALENT_WITH_A_CONSTANT: NOT_PROVED
  FALLING_FINITE_FLOORS_DECIDE_CLASS_SIGN: false
  EULER_GRAM_POSITIVITY_PROVES_THE_FULL_MARGIN_SIGN: false
  SCHUR_FOR_SCALAR_IS_NECESSARY_FOR_FULL_MARGIN: false
CLOSES: [REQ-2026-09-07-SCHUR]
CLOSES_MEANING: requested_paper_review_completed_not_route_state_mutation
CLOSES_ANALYTIC_RH_SUPPLIERS: []
OPENS: []
EVIDENCE_BOUNDARY:
  CUTOFF: f859216e496f54115d4f9b81f8dc78881f2a8e7f
  POST_REQUEST_RESEARCH_RESULTS_USED: false
  OTHER_SCHUR_VERDICT_USED: false
  ALL_SHELF_SHA256_PREFIXES_RECOMPUTED: false
  FINITE_CERTIFICATES: pinned_reports_and_selected_receipts_not_an_independent_rerun
NEW_DERIVATIONS:
  SCOPE: ABSTRACT
  VERIFIER: PAPER
  INDEPENDENT_REVIEW: pending
  LEAN_KERNEL_VERIFIED: false
  HISTORICAL_NOVELTY: not_claimed
EXECUTION:
  HASH_COMPUTATION: true
  NUMERICAL_RUN: false
  SYMBOLIC_SOFTWARE_EXPERIMENT: false
  LEAN_EDIT: false
  ARISTOTLE_SUBMISSION: false
  QUEUE_OR_SHARED_STATE_EDIT: false
PUBLICATION:
  AUTHORIZED_WRITE_SCOPE: VERDICT_DOC_ONLY
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SIGNED_SCHUR_COMPLEMENT_2026-09-07.md
  METHOD: GitHub_create_file_single_document
  COMMIT_AND_READBACK_BLOB: returned_in_delivery_receipt
  RECEIPT_EFFECT: publication_only_not_independent_mathematical_verification
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## 0. Decision and sources

The eight-dimensional result is a finite result. It neither proves the signed complement nor refutes a negative direction outside the packet. The main new derivation below is not another packet: the literal scalar kernel has a **positive dyadic logarithmic principal part**. The rest is smaller in the corresponding energy. This proves the sign of the high-modulation asymptotic and replaces the compact zero-boundary problem by an identity-plus-compact problem in an explicitly defined weaker norm. The remaining finite-inertia obstruction is real and is not declared positive. [ABSTRACT][PAPER]

No complete source contraction or whole-class sum of squares is delivered. Instead, Sections 2--5 give the exact principal square sum, the remaining signed operator, and a scalar positive-extension certificate with an analytic tail. This is a source-specific alternative to treating the pointwise bound O(|xi|^-1/2) as the local spectral order.

Sources actually used, at the request commit unless indicated:

* **[REQ]** The request in the header, read in full through GitHub and independently re-encoded and hashed locally. Both hashes, both counts and final LF match.
* **[R]** `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_RESERVOIR_RESONANCE_AND_PRIME_SCALING_2026-09-06.md`, especially (2), (6), (8), (10)--(16): the source multiplier, cosine series and Mellin conventions.
* **[CF1]** `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CLASS_FLOOR_REPRESENTATION_2026-09-07.md`, blob `b8e9020b5fbe9614fd15beca4aa5ca3c4aae7593`: Sections 4--5 and its prediction ledger.
* **[CF2]** the corresponding `_UPLOADED_VERSION.md`, especially Sections 3.1--3.5 and 4--5. The supplied local version has the same declared SHA-256 `13e0747925b8f61cc861c469093a115558f486cf00ad88bfb42bf59fe6289f9f`; it is evidence for this parent, not a different task. The historical route narratives in other uploads are not used.
* **[LP]** `docs/routeB_bus/LEGENDRE_PACKET_FLOOR_CERTIFICATE_REPORT_2026-09-07.md`; **[LA]** `docs/routeB_bus/phase5_codex/h4_cert/legendre/out/assemble.txt`, blob `795f454fc5777a4bd687e6bdae72df23d76bd81b`. These record the two parity blocks, physical Gram normalization, signed endpoints and the odd upper bound below 1/1000. Their numerical process is not rerun here.
* **[CCM23]** Connes--Consani--Moscovici, arXiv:2310.18423v2, the introduction, (57)--(59), and Theorem 4.6. PDF page 23 was visually checked. It supplies finite-Euler/Sonin correspondence, not positivity of this scalar remainder.
* **[CC20]** Connes--Consani, arXiv:2006.13771v1, the smooth half-line trace framework. The PDF text was available; the requested Appendix screenshot failed. Section 6 below supplies a direct estimate rather than depending on that screenshot.

The independent-check verdicts and numerical agreement described by the observer are corroboration, not assumptions replacing the proofs below. The new source-kernel extraction is a new PAPER derivation and needs independent checking, especially its normalization and resonant-index accounting.

## 1. Conventions and three necessary corrections

Set
\[
 a=\log2,\quad r=2^{-1/2},\quad
 \delta=(\log3-\log2)/8,\quad I=(-\delta,\delta),
\]
\[
 H_{00}=\{h\in L^2(I):\int_Ih(x)e^{x/2}dx=
                            \int_Ih(x)e^{-x/2}dx=0\}.
\]
Use the nonunitary transform \(\widehat h(\xi)=\int h(x)e^{-i\xi x}dx\) and unitary transform \(\mathscr F=(2\pi)^{-1/2}\widehat{\phantom h}\). With zero extension understood,
\[
 b(\xi)=(1-\cos a\xi)\ell_2(\xi),\qquad
 \langle h,\mathcal Th\rangle=-\int b(\xi)|\widehat h(\xi)|^2d\xi
                         =\|h\|^2\mathcal F(h).                 \tag{1}
\]
Thus the uncompressed convolution kernel of \(\mathcal T\) is
\(-\int b(\xi)e^{i\xi t}d\xi\), distributionally. The request's displayed kernel with factor \(-1/(2\pi)\) represents \(\mathcal T/(2\pi)\), not \(\mathcal T\). Its sign is the same, but its numerical coefficients and floors are not. All coefficients below use (1). [ABSTRACT][PAPER]

Second, the source identities are
\[
 \mathfrak m(h)=L_2(v_h)-n_2(v_h)
     =\mathcal F(h)+\|T_{v_h}D_2\|_{HS}^2,
 \qquad \mathcal F(h)=-\operatorname{Tr}
          (T_{v_h}(PQ+QP)T_{v_h}^*).                           \tag{2}
\]
There is a minus sign in front of the anticommutator. Positivity of the Euler-Gram density proves \(n_2\ge0\), **not** \(L_2-n_2\ge0\). The request's Q1(a)(iii) conflates those two values. Third, the signed Schur complement in Q1 is equivalent to scalar-floor positivity, not necessary for full-margin positivity; the second square in (2) can compensate a negative scalar floor.

For example, two rank-one projections with overlap \(0<c<1\) have anticommutator eigenvalues \(c^2+c\) and \(c^2-c\). Neither sign follows from being projections. For \(P=Q\ne0\), the negative of their anticommutator is \(-2P\), not a square. These are exact falsifiers of the proposed abstract shortcuts, not negative directions of the source phase class. [ABSTRACT][PAPER; THEOREM_SHAPE]

## 2. Q1(i),(iv): extract the literal dyadic kernel before estimating it

### 2.1 An elementary cosine integral

Define
\[
 L(z)=\int_0^1(-\log u)\cos(zu)du=\frac{\operatorname{Si}(z)}z,
 \quad L(0)=1,\quad \beta_j=2\pi2^j\ (j\ge0).
\]
The integral defines an entire even function. Integration by parts proves the Si formula. On the real line one may use
\[
 |L(z)|\le\min(1,4/|z|),\quad
 |L'(z)|\le\min(|z|/9,5/|z|^2),\quad
 |L''(z)|\le\min(1/9,12/|z|^2).                              \tag{3}
\]
For the large-argument bounds use \(|\operatorname{Si}z|\le4\),
\(L'=(\sin z-\operatorname{Si}z)/z^2\), and differentiation once more. The small-argument bounds follow directly from the integral. Constants are deliberately conservative. [ABSTRACT][PAPER]

Put
\[
 S(t)=\sum_{j\ge0}L(\beta_jt),\qquad t\ne0.                 \tag{4}
\]
This is locally integrable, with a logarithmic singularity at zero; do not assign it a finite value at zero. Indeed
\(\int_{-d}^d|L(\beta t)|dt\le C_d(1+\log\beta)/\beta\) for \(\beta\ge1\), by (3). The series converges in local L1 and as a convolution operator on a fixed bounded interval. Each summand is positive definite, because it is an integral of cosines with nonnegative weight. Consequently S defines a positive quadratic form.

### 2.2 Exact kernel from the source, not from a fitted amplitude

Let \(c_{-1}=-1/2,\ \beta_{-1}=\pi\), and \(c_j=1/2\) for \(j\ge0\). For a finite Euler partial sum the log-coordinate Fourier kernel is
\[
 H_J(s)=2e^{s/2}\sum_{j=-1}^{J}c_j\cos(\beta_je^s).
\]
Its full Mellin transform is \(\gamma_J(\xi)=\int H_J(s)e^{i\xi s}ds\), distributionally, and
\(t_J=(2\pi)^{-1}\widehat{(-s)_+H_J}(\xi)\).
Thus the inverse Fourier kernel of \(\ell_J=2\Re(\gamma_Jt_J)\) is
\[
 K_{\ell,J}(t)=\frac{I_J(t)+I_J(-t)}{2\pi},
\quad I_J(t)=\int_{-\infty}^{0}(-s)H_J(s)H_J(s+t)ds.
\]
All integrals for fixed J and bounded t are ordinary convergent integrals. The product-to-sum identity gives the explicit formula
\[
 K_\ell(t)=\frac1\pi\sum_{i,j\ge-1}c_ic_j\left\{
 e^{t/2}[L(\beta_i-\beta_je^t)+L(\beta_i+\beta_je^t)]
 +e^{-t/2}[L(\beta_i-\beta_je^{-t})+L(\beta_i+\beta_je^{-t})]
 \right\}.                                                   \tag{5}
\]
The meaning is local L1 convergence around each of \(0,a,-a\), not an absolute pointwise value at those three singular points.

Here is the convergence check. Choose
\[
 d_0=a/4>2\delta.
\]
On \(t=ka+z,\ |z|\le d_0,\ k=0,\pm1\), the only infinitely recurring small differences in (5) are \(i-j=k\) in the first exponential term and \(i-j=-k\) in the second, with \(i,j\ge0\). Their series are scaled copies of (4), so converge locally in L1. All remaining differences, apart from finitely many low-index terms, obey
\[
 |\beta_i-\beta_je^{\pm t}|\ge\kappa\max(\beta_i,\beta_j),
 \quad \kappa=e^{-a-d_0}(1-e^{d_0}/2)>0.
\]
The sum arguments have the same lower bound. Equation (3), including one derivative in z, bounds a nonresonant pair by \(C/\max(\beta_i,\beta_j)\). There are O(n+1) pairs with maximum index n; \(\sum(n+1)2^{-n}<\infty\). Their sum is C1 on these intervals.

Finally \(\gamma_J\to\gamma_2\) uniformly by the norm-convergent Euler multiplier, and \(t_J\to t_2\) uniformly by the proved Mellin tail. Hence \(\ell_J\to\ell_2\) uniformly, which identifies the local L1 limit of (5) with the actual inverse Fourier distribution of \(\ell_2\). No square of the bare lacunary distribution, or untested infinite trace, is used. This proves (5). [ABSTRACT][PAPER; source R (8),(10)]

### 2.3 The resonant-index calculation

Write
\[
 D(t)=e^{t/2}S(1-e^t)+e^{-t/2}S(1-e^{-t}).
\]
The resonant part of \(K_\ell(t)\) near zero is \(D(t)/(4\pi)\). Near \(a\), it is
\[
 \frac1{4\pi}\{\sqrt2e^{t/2}S(2(1-e^t))
                 +r e^{-t/2}S(1-e^{-t})\},
\]
where t now denotes displacement from a. Near \(-a\), it is
\[
 \frac1{4\pi}\{r e^{t/2}S(1-e^t)
                 +\sqrt2e^{-t/2}S(2(1-e^{-t}))\}.
\]
These expressions follow by listing respectively \(i=j\), \(i=j+1\), and \(j=i+1\). The terms involving index -1 contribute only to the regular remainder.

Multiplication by \(1-\cos(a\xi)\) replaces the kernel by its value minus half of each translate. Use the exact identity
\[
 S(2z)=S(z)-L(2\pi z).
\]
Then multiply by \(-2\pi\), as required by (1). The result is
\[
 \boxed{K_{\mathcal T}(t)=cS(t)+R(t),\quad
            c=\cosh(a/2)-1>0,\quad R\in W^{1,1}(-d_0,d_0).}    \tag{6}
\]
This is the uncompressed kernel; apply the unchanged moment projection at both ends.

For clarity, (6) defines R without an unknown spectral object. Let \(N_0(t),N_+(t),N_-(t)\) be (5), evaluated at \(t,t+a,t-a\), after subtracting just the displayed resonant series. Then
\[
\begin{split}
 R(t)={}&\frac c2[D(t)-2S(t)]
 -\frac{\sqrt2}{4}\{e^{t/2}L(2\pi(1-e^t))
                    +e^{-t/2}L(2\pi(1-e^{-t}))\}\\
 &-2\pi[N_0(t)-\tfrac12N_+(t)-\tfrac12N_-(t)].              \tag{7}
\end{split}
\]
All finite exceptional terms are retained in the N terms.

**Regularity proof for the one nontrivial remainder.** For \(|t|\le d_0<1/4\), put
\(q_\beta(t)=e^{t/2}L(\beta(e^t-1))-L(\beta t)\).
Then
\[
 \|q_\beta\|_{W^{1,1}(-d_0,d_0)}\le2048\,\beta^{-1/2}
                         \quad(\beta\ge1).                 \tag{8}
\]
To verify a bound with this constant, use \(|e^t-1-t|\le t^2\),
\(|e^t-1|/|t|\in[1/2,2]\), and differentiate q. The derivative is the sum of
\[
 (e^{t/2})'L(\beta(e^t-1)),\quad
 (e^{3t/2}-1)\beta L'(\beta(e^t-1)),\quad
 \beta[L'(\beta(e^t-1))-L'(\beta t)].
\]
For the last term (3) gives the three useful bounds
\(\beta^2t^2/9,48,25/(\beta t^2)\). Integrate them on
\(|t|\le\beta^{-1}\), \(\beta^{-1}<|t|\le\beta^{-1/2}\), and the rest, truncating at d0. The first two derivative terms cost O((1+log beta)/beta) using (3) and \(|e^{3t/2}-1|\le3|t|\). Their displayed constants, the two sides of the interval, and \(q_\beta(0)=0\) give less than 2048 beta^-1/2 for the full W1,1 norm. For 1<=beta<=16 the elementary small-argument bounds alone give the same conservative allowance. Summing (8) over beta_j proves \(D-2S\in W^{1,1}\); the N terms were already C1. This completes the proof of (6).

This positive principal coefficient comes from **the two translated resonance families**, not from declaring the original multiplier nonnegative. Omitting either family changes the coefficient and invalidates the result.

## 3. Positive principal square sum and the high-frequency sign

The source-defined principal form in (6) is
\[
 \mathcal P[h]=\frac c2\sum_{j\ge0}\int_0^1(-\log u)
       (|\widehat h(\beta_ju)|^2+|\widehat h(-\beta_ju)|^2)du.
                                                               \tag{9}
\]
It is a convergent sum of nonnegative terms on the fixed supported space. Equivalently,
\[
 \mathcal P[h]=\frac1{2\pi}\int p(\xi)|\widehat h(\xi)|^2d\xi,
 \quad p(\xi)=c\pi\sum_{j\ge0}\frac1{\beta_j}
                  \log\frac{\beta_j}{|\xi|}\,1_{|\xi|<\beta_j}.
                                                               \tag{10}
\]
The locally integrable logarithmic singularity of p at zero is intentional. A value at the single point zero is immaterial. Positivity follows directly from the weights; it is not inferred from the desired class sign.

For \(T\ge2\pi\), let J be the least integer with \(\beta_J\ge T\), and put
\(\theta_T=\log(\beta_J/T)\in[0,a]\), identifying the equal endpoint values. Geometric summation gives
\[
 \boxed{p(T)=\frac{2\pi c}{T}e^{-\theta_T}(\theta_T+a).}       \tag{11}
\]
In particular, with
\[
 c_*=2\pi c a,\qquad C_*=4\pi c/e,
\]
\[
 \boxed{c_*/T\le p(T)\le C_*/T\quad(T\ge2\pi),\qquad
             \sup_{\xi\ne0}|\xi|p(\xi)=C_*.}                \tag{12}
\]
For all real xi, \(p(\xi)\ge c_*/(2\pi+|\xi|)\). The minimum of
\(e^{-\theta}(\theta+a)\) on [0,a] is a; its maximum is 2/e. Formula (11) has a logarithmically periodic coefficient. A claim of one limiting value for Tp(T) would be false.

Choose an even C2 cutoff chi equal to one on [-2delta,2delta] and zero outside (-d0,d0), and define \(R_c=\chi R\). A concrete choice is the quintic smoothstep on each transition interval; its first two derivatives vanish at both transition ends. Put \(r_c=\widehat{R_c}\). Equations (1),(6) imply the exact identity
\[
 \boxed{\|h\|^2\mathcal F(h)
   =\frac1{2\pi}\int[p(\xi)+r_c(\xi)]|\widehat h(\xi)|^2d\xi.}\tag{13}
\]
It holds for every supported L2 test, followed by the moment restriction. Since \(R_c\in W^{1,1}_c\), integration by parts and Riemann--Lebesgue give
\[
 r_c(\xi)=o(|\xi|^{-1}).                                    \tag{14}
\]
The modified multiplier in (13) need not equal \(-2\pi b\) pointwise on the entire frequency line: it gives the **same compressed form**, because their spatial kernels agree on I-I. This is an intentional, exact representation change.

### Theorem 1. High modulation approaches zero from above

For any fixed nonzero \(\eta\in C_c^\infty(I;\mathbb C)\), put
\[
 h_T=(\partial_x^2-1/4)(e^{iTx}\eta(x)).
\]
Both pole moments vanish exactly. Then
\[
 \boxed{\mathcal F(h_T)=p(T)+o(T^{-1})>0\quad\text{eventually}.}\tag{15}
\]
In particular \(\mathcal F(h_T)\ge c_*/(2T)\) for all sufficiently large T, with the threshold allowed to depend on eta. The full margin is at least this floor by (2).

**Proof.** \(\widehat h_T(\xi)=-(\xi^2+1/4)\widehat\eta(\xi-T)\) and
\(\|h_T\|^2/T^4\to\|\eta\|^2\). The function p is continuous across its dyadic knots and has derivative bounded by C/T^2 in a fixed relative neighborhood of large T. In (10), set xi=T+s. On |s|<=T/2, Taylor's Lipschitz bound and the Schwartz moments of eta replace p(T+s) by p(T) with O(T^-2) normalized error. Outside that band rapid decay handles the logarithmic singularity at xi=0 and all the tails. Parseval supplies the normalization 2pi.

For the remainder, write h_T=e^{iTx}T^2 eta_T, with eta_T converging in every fixed smooth seminorm to -eta. The remainder quadratic value is a Fourier integral of R_c times the compactly supported autocorrelation of eta_T. That product converges in W1,1 to the corresponding product for eta; its derivative has a Riemann--Lebesgue transform. Integration by parts proves a normalized o(1/T) remainder. Equations (11)--(12) prove the sign. The real cosine-modulated version has the same leading term: the two separated Fourier peaks contribute equally and their cross term is rapidly decreasing. QED. [ABSTRACT][PAPER]

This is **not** a sign proof on all tests. A negative finite-rank smooth perturbation can preserve (15) while making an untested low-frequency direction negative; Section 5 gives that falsifier.

### A precise second-difference family

Finite packet coefficients do not specify a unique asymptotic family. For the natural exact family, define
\[
 h_k=(\partial^2-1/4)(1-(x/\delta)^2)^k_+,
 \quad g_k=h_k-2h_{k+1}+h_{k+2}
        =(\partial^2-1/4)[z^4(1-z^2)^k]_+ .                 \tag{16}
\]
Here the subscript means zero extension on |z|<1, not taking a positive part of h. Then
\[
 \boxed{\mathcal F(g_k)=\Theta(k^{-1/2})>0\quad\text{eventually}.}\tag{17}
\]
This does not assert that the measured minimizers equal (16).

**Proof with the leading expression.** Set epsilon=delta/sqrt(k) and f(y)=y^4 exp(-y^2). After an irrelevant scalar multiplication the primitive in (16), at x=epsilon y, is
\(f_k(y)=y^4(1-y^2/k)^k1_{|y|<\sqrt k}\).
For every fixed derivative and polynomial weight, f_k converges to f in the corresponding L1 and L2 seminorms. This follows by differentiating the polynomial, using
\((1-y^2/k)^{k-m}\le e^{-y^2/2}\) for k>=2m, and dominated convergence; endpoint derivatives of the required fixed orders vanish once k is large.

For the scaled differentiated profile, change variables s=epsilon xi in (13). If \(\sigma(t)=tp(t)\) for t>0, the resulting leading expression is
\[
 \mathcal F(g_k)=\frac{\epsilon}{2\pi\|f''\|^2}
   \int_{\mathbb R}\sigma(|s|/\epsilon)|s|^3|\widehat f(s)|^2ds
   +o(\epsilon).                                           \tag{18}
\]
To justify the limit use (12), the uniform seminorms just proved and (14). The region |s|<=2pi epsilon contributes o(epsilon); the lower derivative term -eta/4 also contributes o(epsilon). On its complement sigma lies between c_* and C_*. The positive integral of |s|^3|hat f|^2 proves (17). The coefficient in (18), too, may oscillate with log epsilon. This proof applies in the polynomial form domain already justified by the parents, and then to smooth approximants with the stated norm error. QED.

## 4. Q1: the exact intermediate object and a new signed-complement route

### 4.1 What the candidate representations do and do not establish

The kernel before compression is of difference type. Calling it Hankel after reflection, or Loewner without divided-difference data, supplies no positivity theorem. A Fejer--Riesz factorization of the original sign-changing multiplier is not available just because two moments vanish. For a nonzero compactly supported smooth test its transform is entire and cannot vanish on an open frequency interval. Therefore a nonempty open negative-frequency part is not literally annihilated by the moment conditions. Compensation, rather than deletion, would have to be proved.

The source anticommutator shortcut fails with the sign and projection counterexamples in Section 1. The Euler-Gram picture proves positivity of the reservoir n2 only; its subtraction from L2 still requires comparison. The unchanged abstract Schur identity remains correct, but asserting the sign of its remainder would simply assume scalar positivity. Equations (6)--(13) provide an additional **source formula**, not that assertion. [ABSTRACT][PAPER]

### Theorem 2. Relative compactness and finite negative inertia

Complete H00 in the principal norm \(\|h\|_{\mathcal P}^2=\mathcal P[h]\), obtaining a Hilbert space E00. There is a source-defined compact self-adjoint operator K_rel on E00 such that
\[
 \boxed{\|h\|^2\mathcal F(h)
       =\langle h,(I+K_{\rm rel})h\rangle_{\mathcal P}.}       \tag{19}
\]
Thus scalar positivity is equivalent to \(I+K_{\rm rel}\succeq0\). In this representation the essential spectrum is {1}. There are only finitely many negative directions, counted with multiplicity, and finitely many possible zero directions. Their number and signs have **not** been determined.

**Proof.** By (12), the principal norm dominates the full-line H^-1/2-type norm with weight c_*/(2pi+|xi|). Every polynomial or exponential moment on the fixed interval is continuous for this norm: insert a smooth cutoff equal to one on I and apply weighted Fourier Cauchy--Schwarz. In particular the moment-null completion is well defined.

Define the remaining form by
\((2\pi)^{-1}\int r_c\overline{\widehat h}\widehat g\).
The ratio r_c/p is bounded and tends to zero at infinity by (12),(14); hence this form is bounded in principal norm. On each finite frequency band the map h -> hat h is compact from the supported energy completion into L2 of that band. Indeed the same cutoff/Cauchy--Schwarz estimate bounds both evaluation and its frequency derivative uniformly on the band; Arzela--Ascoli proves compactness. Equivalently, Taylor approximation of exp(-i xi x) there yields finite-rank moment maps with an error tending to zero in the weighted dual norm. The low-band remainder is therefore compact, and its high-band principal-relative norm tends to zero. Riesz representation proves compactness and self-adjointness of K_rel, and (13) proves (19).

The compact self-adjoint spectral theorem leaves only finitely many eigenvalues of K_rel at or below -1. Density of supported smooth moment-null tests in E00 means that a negative direction in the completion is approximable by genuine negative test directions. It follows that the original form has finite negative inertia too. This is not a claim that the original L2 operator has a positive uniform gap. QED. [ABSTRACT][PAPER]

The representation preserves the whole complex moment-null class and its form values. It does not discard low modes or add an identity to the original form: the identity in (19) is the exact positive source form (9), expressed in its own energy.

### 4.2 A quantitative route to a certificate, without another raw packet

The following sufficient object is scalar and has a signed tail:
\[
 \boxed{p(\xi)+\widehat{\chi R}(\xi)\ge0\quad(\xi\in\mathbb R).}\tag{20}
\]
If proved, (13) becomes the required whole-class square
\((2\pi)^{-1}\|\sqrt{p+\widehat{\chi R}}\,\widehat h\|_2^2\), and (2) adds the other source square. The cutoff chi is fixed above before any test. A failure of (20) refutes this extension certificate, **not** necessarily the compressed scalar form; another extension or (19) may work.

Here is a completely specified way to bound the omitted source series. Construct R_J from (7) by keeping the nonresonant pairs with maximum index at most J, all finite exceptional terms, and the first J+1 terms of D-2S. Let R_c,J=chi R_J, and take J>=2. Put
\[
 E=e^{(a+d_0)/2},\quad B=e^{a+d_0},\quad
 C_N=256(1+d_0)E(1+6/\kappa+5B/\kappa^2),\quad
 C_\chi=1+\|\chi'\|_\infty.
\]
The estimates used in (5),(8) give the conservative bound
\[
 \boxed{\|R_c-R_{c,J}\|_{W^{1,1}}\le e_J:=C_\chi\left[
 C_N\frac{(2J+7)2^{-J}}{2\pi}
 +4096(1+c)\frac{r^{J+1}}{\sqrt{2\pi}(1-r)}\right].}          \tag{21}
\]
For the first term count the 2n+3 pairs at maximum index n and use the nonresonant C1 bound following (5). The sum is (2J+7)2^-J. The four kernel branches, the three shifted locations and their coefficients are dominated by C_N as written. The second term is (8) for the two nonlinear resonant terms, followed by a geometric sum. Multiplication by chi costs at most C_chi. No fitted oscillation constant occurs.

Let \(D_J=\|R_{c,J}''\|_1\), a finite explicit integral of derivatives of L and exponentials. Two integrations by parts for R_c,J and one for the omitted derivative give
\[
 |\widehat{\chi R}(\xi)|\le D_J/|\xi|^2+e_J/|\xi|.
\]
Consequently, if e_J<c_*, the tail in (20) is nonnegative whenever
\[
 \boxed{|\xi|\ge\max(2\pi,D_J/(c_*-e_J)).}                  \tag{22}
\]
Near zero p tends to +infinity while |hat(chi R)|<=||chi R||_1. Only the resulting intervening compact band needs a signed enclosure. Its integrand is a spatial finite-series Fourier integral with remainder e_J, not the ill-conditioned semilocal inverse. Constants (21) are deliberately coarse; no claim of an economical cutoff or a completed numerical certificate is made.

The alternative is to certify (19). A full error bound
\(\|K_{\rm rel}-\Pi K_{\rm rel}\Pi\|\le\eta<1\) in the **principal energy**, and a head lower bound
\(\Pi(I+K_{\rm rel})\Pi\ge\alpha\Pi\), suffice if
\[
 \alpha-\eta^2/(1-\eta)\ge0.                               \tag{23}
\]
This is the ordinary signed Schur estimate with a genuine complement floor 1-eta. A high-frequency contribution to eta is bounded by
\(e_J/c_*+D_J/(c_*Y)\) beyond |xi|=Y. The remaining band can be approximated by the finite-rank moment maps in the proof of Theorem 2, retaining their weighted dual-norm errors. The old L2 packet Gram and old unsigned tail do not equal these principal-energy objects. Computing or bounding that finite-band approximation is a separate explicit certificate task.

Equation (23) can give a finite positive decision when I+K_rel is strictly positive. If it has exact zero modes, those modes and their couplings still require a structural nullspace certificate. No universal finite-time exact-boundary decider is asserted.

## 5. Strongest attack and the scope of the new result

A positive principal kernel and the high-modulation sign do not settle the finite remainder. Choose a nonzero smooth pole-null g L2-orthogonal to the eight frozen tests; such g exists because the constraints are finite. The auxiliary operator
\[
 \widetilde{\mathcal T}=\mathcal T-M|g\rangle\langle g|
\]
has the same eight-dimensional compression. For sufficiently large M, its value on g is strictly negative. The perturbation has a smooth kernel and does not change the principal term (6), the high-modulation asymptotic (15), or finite negative inertia. This exact example refutes the inference that the new asymptotic plus the eight positive directions proves PSD. It is not the source operator and is not a source counterexample. [ABSTRACT][PAPER; THEOREM_SHAPE]

The minimal original scalar inequality remains
\[
 -\int (1-\cos a\xi)|\widehat h|^2\ell_2\,d\xi\ge0
                         \quad(h\in H_{00}).                \tag{24}
\]
The new equivalent intermediate object is (19); the new independently checkable sufficient object is (20). These do not claim that the two pole constraints annihilate every negative frequency, and they do not identify n2 with the margin.

## 6. Q2: explicit trace-norm exponent, pinching, and the diagonal

### 6.1 A weighted Hankel bound

For a Schwartz function k put
\[
 N(k)^2=\sum_{j=0}^2\int_{\mathbb R}(1+|t|)^5|k^{(j)}(t)|^2dt.
\]
The same-half-line integral operator with kernel k(x+y+s) satisfies
\[
 \boxed{\|H_{k,s}\|_1\le216(1+|s|)^3N(k).}                 \tag{25}
\]
Both half-line orientations are allowed, with k or its reflection.

**Proof.** On the positive quadrant extend the kernel by chi0(x)chi0(y)k(x+y+s), where chi0=0 for x<=-1, chi0=1 for x>=0, and on [-1,0] it is the quintic smoothstep. It has |chi0'|<=2 and |chi0''|<=6. Let H=1+x^2-d^2/dx^2 on L2(R). Its eigenvalues are 2n+2, so ||H^-1||_HS=pi/(2sqrt(6))<1. The trace-ideal product inequality gives
\(\|T_K\|_1\le\|H^{-1}\|_{HS}\|H_xK\|_{L^2(\mathbb R^2)}\).
The differentiated kernel is bounded in modulus by
\((x^2+7)|k|+4|k'|+|k''|\).
Writing u=x+y>=-2, integration over x in [-1,u+1] bounds its squared L2 norm by
\(192\sum_{j=0}^2\int_{-2}^\infty(u+3)^5|k^{(j)}(u+s)|^2du\).
Since u+3<=3(1+|u+s|)(1+|s|), this is at most
\(216^2(1+|s|)^5N(k)^2\). Restriction back to the quadrant cannot increase trace norm. Replacing the exponent 5/2 by 3 proves (25). The extension has the required weak second derivatives, so the oscillator factorization is legitimate. QED. [ABSTRACT][PAPER]

Let k_v be the inverse multiplier kernel of \(\widehat v\,m_\infty\), where \(m_\infty=\gamma_\infty(-\cdot)\). It is Schwartz. The two off-diagonal quadrants of [T_v,P] and (25) imply
\[
 \|[T_v,P]\|_1\le432N(v),
\]
\[
 \boxed{\|T_vPU_sF_\infty P\|_1
   \le432N(v)+216(1+|s|)^3N(k_v).}                          \tag{26}
\]
Indeed commute T_v past P; the first term is [T_v,P] times contractions, and the second is the shifted half-line Hankel kernel k_v. Appending the bounded external F_S T_v* costs at most ||v||_1. This is the explicit exponent requested in Q2(a).

For the prime-2 Euler expansion its trace-norm majorant uses
\[
 (1-r^2)\sum_{j\ge0}r^j(1+ja)^3+r(1+a)^3<\infty,
\]
\[
 \sum_{j\ge0}r^j(1+ja)^3
 =\frac1{1-r}+\frac{3ar}{(1-r)^2}
 +\frac{3a^2r(1+r)}{(1-r)^3}
 +\frac{a^3r(1+4r+r^2)}{(1-r)^4}.                           \tag{27}
\]
Finite products of prime factors remain summable by the corresponding multi-index polynomial bound. Constants depend on the fixed prime set and the test; uniformity as that set grows is not asserted.

### 6.2 Pinching and the continuous tested diagonal

For orthogonal projections E_n->I strongly and K trace class,
\[
 \|E_nKE_n-K\|_1\le\|(E_n-I)K\|_1+\|K(E_n-I)\|_1\to0.    \tag{28}
\]
Proof: approximate K in trace norm by a finite-rank operator, use strong convergence on its finite left and right ranges, and use ||E_n||<=1 for the two remaining errors. This is the standard trace-ideal finite-rank-density lemma, with its proof supplied here.

Strong convergence alone for arbitrary non-self-adjoint E_n is not sufficient: E_n=I+|e_0><e_n| and K=|e_0><e_0| give E_n->I strongly but E_nKE_n-K=|e_0><e_n| of trace norm one. The source uses orthogonal band/step projections, so (28) applies. [ABSTRACT][PAPER]

On a finite frequency band a continuous kernel K has
\[
 \operatorname{Tr}(E_nKE_n)=
  \sum_{J\in\mathcal P_n}\frac1{|J|}\int_{J\times J}K(\xi,\eta)d\xi d\eta
       \longrightarrow\int K(\xi,\xi)d\xi.
\]
Uniform continuity proves this limit; (28) identifies it with the trace when K is trace class. First use it for each finite Euler kernel, then use (26)--(27) to pass the Euler sum in trace norm and the uniform scalar Mellin convergence to pass the diagonals. Finally remove the band using (28) and the integrable tested multiplier. This is precisely the mechanism in CF2 Section 3.5 needed by CF1 Section 4.4. No assertion about the diagonal of an arbitrary merely measurable trace-class kernel is being used. [ABSTRACT][PAPER]

## 7. Q3: actual spectral information versus a fitted 1/k plot

For a nested dense sequence of finite subspaces, the exact smallest Rayleigh values decrease to inf Spec(T). This follows by approximating any fixed unit vector with normalized projections. Computed lower endpoints need not themselves be monotone under arbitrary changes in error budgets. The supplied four finite values do not determine the limit.

For this source the new kernel derivation gives more than the old O(xi^-1/2) pointwise envelope. In fact
\[
 \boxed{s_{n+1}(\mathcal T)\le
 \frac{2\delta}{\pi n}\left(C_*+\|R_c'\|_1\right),\quad n\ge1.}\tag{29}
\]
To prove it, (12) shows that convolution with cS maps supported L2 inputs into functions whose derivative has full-line L2 norm at most C_*||h||. The remainder derivative costs ||R_c'||_1||h|| by Young's inequality. Approximate the output on I by its mean on n equal subintervals. The mean-zero Poincare inequality gives error at most (2delta)/(pi n) times the derivative norm. Applying P00 at the output and input does not increase the error or rank. The approximation-number characterization of singular values proves (29). [ABSTRACT][PAPER]

This is an upper rate with an explicit source constant, **not an exact Weyl equivalent**. Smoothness of b together with an oscillatory decay envelope alone is insufficient to apply a classical homogeneous-symbol Weyl law: its derivatives need not satisfy that symbol class, and oscillation can translate singularities away from the compressed diagonal. Here the dyadic calculation identifies the positive local order-one kernel and the nonconstant log-periodic coefficient (11). No formula lambda_n~C/n for this interval operator is proved in this verdict.

If an N-dimensional head has a strictly positive lower Rayleigh value l_N, min--max gives l_N<=s_N(T). Thus an independently proved all-N bound l_N>=cN^-alpha with alpha<1 would eventually contradict (29), not certify PSD by matching a plot. If every head in a dense family were proved nonnegative, positivity would follow directly by continuity, with no rate conjecture needed. Four observed values near 1/k imply neither assertion. The finite-rank negative perturbation in Section 5 preserves both the local spectral order and any finite initial head history. [ABSTRACT][PAPER]

For completeness, the declared Legendre family is dense in H00, not just plausibly oscillatory. Given smooth pole-null h, solve
\(\eta''-\eta/4=h\) with zero value and derivative to the left of its support:
\(\eta(x)=\int_{-\delta}^x2\sinh((x-y)/2)h(y)dy\).
The two moment conditions make eta vanish to the right of the support too. Then eta/eta4 is smooth and compactly supported inside I. Approximate it and its first two derivatives uniformly by polynomials; multiplication by eta4 and application of the differential operator approximate h in L2. Standard two-moment correction proves density of smooth moment-null tests in H00. This proves density of the fixed Legendre-generated union, in both parities. It supplies the quantifier interface, not positivity of all its members.

The practical discriminator has therefore changed: the new theorem rules out an infinite sequence of independent negative directions accumulating at zero, but still permits finitely many unobserved negative directions. Decide those through (19)--(23) or an actual negative test, not through the slope of four positive floors.

## 8. Q4: an actual exhaustion and what this class buys

### 8.1 Full classes, joint spans, and pole directions

A definite exhausting family in log coordinates is
\[
 \mathscr D_R=C_c^\infty((-R,R);\mathbb C),\quad R=1,2,\ldots .\tag{30}
\]
Every compact smooth test belongs to one member. Positivity on each **full complex linear class** therefore suffices for the terminal all-test requirement. For a numerical/formal implementation one may take directed finite spans of chi_r(x)x^j with integers r<=R and j<=N, where chi_r is a fixed smooth bump supported in [-r,r], positive in its interior. On any fixed support, divide the desired test by a bump on a slightly larger window and approximate in every required C^k norm by polynomials. Multiplication by the fixed bump gives compact smooth approximants. Positivity of every joint finite-span matrix and continuity of the actual Weil form then suffices. A collection of positive individual vectors is not that premise.

At window R, autocorrelation is supported in [-2R,2R]; include every prime power n with log n<=2R. A finite place set containing the primes up to exp(2R) suffices for the arithmetic terms at that window, with the archimedean and pole terms unchanged. Increasing R brings all compact tests and all relevant prime powers. This is the finite-prime/exhaustion setting described in CCM23's introduction; it is not a claim that any such full window has now been proved positive. [ABSTRACT][PAPER, conditional positivity premise explicit]

Unions of the present minus-lobe classes, even with all prime distances and translations, do not give (30). Their generators have integral zero and both exponential moments zero. On a fixed support these are continuous constraints; their span cannot approximate an arbitrary test with nonzero moments in the test-function topology. Even within the pole-null space, individual two-lobe positivity does not establish all mixed values of their span. For example the form |x|^2+|y|^2-3Re(conj(x)y) is positive on each coordinate axis and negative at (1,1).

A pole-null-only strategy needs an additional finite-rank completion: choose two fixed compact smooth anchor functions with independent exponential moments, decompose each test into its moment-null part plus those anchors, and prove the full 2-by-2 anchor/coupling Schur statement. Those couplings are not supplied by (24). Alternatively prove (30) directly, retaining the pole terms. No density claim discards them.

### 8.2 What T>=0 here would actually give

It would prove, for every h in this fixed moment-null short window, the full prime-2 test value
\[
 Q(v_h)=L_2(v_h)\ge n_2(v_h)\ge0,
\quad v_h=(U_{a/2}h-U_{-a/2}h)/(\sqrt2\|h\|).
\]
The support diameter is a+2delta<log3, so only the atom at log2 is present, and the pole terms vanish. This is a genuine restricted Weil inequality. It is not by itself a zero-free region or a zero-location theorem, because the terminal criterion quantifies all tests and no isolating-test inclusion theorem for this restricted class has been supplied. Nor is autocorrelation of a test at log2 a theorem about statistical pair correlation of zeta zeros. The exact zero-side explicit formula can re-express the restricted inequality, but adds no missing test quantifier. [ABSTRACT][PAPER]

### 8.3 The next classes and what must be rederived

The cheapest enlargement **before adding a prime** removes the shared-profile/minus-only restriction:
\(v=U_{a/2}h_++U_{-a/2}h_-\), with independent pole-null profiles in I. One must certify the joint operator matrix, including its cross terms and all complex phases. The source pair and arithmetic cutoff remain unchanged.

The first clean enlargement carrying both primes is three lobes at centers 0, log2, log3, each with radius delta and with independent profiles and coefficients. Its diameter log3+2delta is less than log4. Only prime powers 2 and 3 occur; the other lobe difference log(3/2) is not an arithmetic atom, though the analytic mixed energy remains. Use the finite-Euler map
\(B_{2,3}=(I-2^{-1/2}U_{\log2})(I-3^{-1/2}U_{\log3})\).
The abstract projection-square and image-Gram identities transfer. The Mellin series becomes a two-index series, the scalar remainder and its sign must be rederived, and the clean single-dyadic local resonance separation in Section 2 does not transfer verbatim: log-ratios of powers of 2 and 3 can be arbitrarily close. Neither parity nor the exact old numerical bounds may be imported unchanged unless the new class has the relevant symmetry.

The Sonin cutoff is a separate parameter. For P_lambda=1_{x<log lambda}, the tested arithmetic trace acquires the explicit term
\[
 \operatorname{Tr}(T_v(I-P_\lambda-F_SP_\lambda F_S)T_v^*)
       =L_S(v)-2\log\lambda\,\|v\|^2.                       \tag{31}
\]
Indeed reflection replaces P_lambda by I-P_{1/lambda}; the remaining difference of half-line cutoffs has length 2log lambda with the displayed sign. The abstract square algebra survives, but the scalar cutoff integrals, additive term, source kernels and certificate budgets change. One may keep lambda=1 while exhausting the test support and finite prime sets; varying lambda is not a substitute for that exhaustion.

## 9. Prediction ledger and evidence grades

The observer probabilities and events are preserved. A mathematical nonachievement below is not scored as a proof of the opposite sign.

| Frozen observer event | p | Fate |
|---|---:|---|
| P_SIGNED_COMPLEMENT_CONSTRUCTED | 0.15 | NOT_ACHIEVED. A positive principal square sum is constructed; its signed remainder is not proved positive. |
| P_STRUCTURAL_ROUTE_NAMED | 0.50 | CONFIRMED_ON_PAPER: dyadic positive kernel plus W1,1 remainder, relative compactness (19), and the explicit positive-extension inequality (20). |
| P_HIGH_MODULATION_SIGN_FROM_ABOVE | 0.55 | CONFIRMED_ON_PAPER by (11)--(15); the leading coefficient is log-periodic, and the threshold depends on the fixed envelope. |
| P_TWO_LEMMAS_WRITTEN | 0.85 | CONFIRMED_ON_PAPER: exponent 3 in (26)--(27), pinching (28), and the continuous-band diagonal argument. |
| P_FLOOR_DECAY_DIAGNOSTIC | 0.40 | NOT_ACHIEVED_AS_REQUESTED. An analytic O(1/n) upper bound is proved, but matching the observed 1/k is not a usable one-sided sign discriminator. |
| P_EXHAUSTION_STRUCTURE_GIVEN | 0.60 | CONFIRMED_ON_PAPER by (30)--(31), joint-span requirements, pole completion, and the two explicit next classes. |

Earlier CLASSFLOOR forecasts, exact names rather than the shortened aliases in the request:

| Frozen registration | p | Current fate |
|---|---:|---|
| P_CF_SOURCE_NUCLEARITY_AND_MELLIN_LIMIT_SURVIVES | 0.91 | CONFIRMED_ON_PAPER at the named domain; Section 6 supplies the previously qualitative exponent and diagonal limit. |
| P_CF_CONSTANT_120_SURVIVES | 0.97 | RETAINED: 18+72sqrt(2)<120 and the previous analytic argument is unchanged; no new interval run or reallocation is claimed here. |
| P_CF_FIRST_ODD_PACKET_HAS_NO_CERTIFIED_NEGATIVE_DIRECTION | 0.60 | CONFIRMED_FROM_PINNED_INTERVAL_RECORD [LP,LA], on precisely that packet. |
| P_CF_SOURCE_TRACE_DOMAIN_REVIEW_SURVIVES | 0.86 | CONFIRMED_ON_PAPER with the explicit trace estimate and the orthogonal-projection assumptions of Section 6. |
| P_CF_EXPLICIT_128_MAJORANT_SURVIVES | 0.94 | RETAINED at its checked paper status; not inferred from the new packet numbers. |
| P_CF_PACKET_OUTWARD_RECEIPT_PRESERVES_1_OVER_1000 | 0.98 | CONFIRMED_AS_REPORTED_REPAIRED_RECEIPT in REQ/LP; no reassembly is rerun here and no new last-digit claim is made. |
| P_CF_ODD_TWO_TEST_SCALAR_PACKET_NONNEGATIVE | 0.55 | CONFIRMED_FROM_PINNED_INTERVAL_RECORD: x eta4 and x eta5 lie in the certified odd span before applying the same differential operator. |

CF1's already closed local registrations (0.78 tested domain, 0.75 static packet audit, 0.99 unsigned-complement obstruction) are preserved, not newly rescored as blind predictions. The frozen exponential-bump event is still not tested by substituting the polynomial h4. The request's stronger numerical record does not turn these new PAPER derivations into LEAN proofs.

New prospective registrations concern future independent audits, not tests performed here:
```yaml
P_SCHUR_DYADIC_KERNEL_AND_COEFFICIENT_SURVIVES:
  probability: 0.85
  event: independent_source_audit_accepts_5_to_14_including_the_2pi_factor_and_all_three_resonance_families
  fate: PENDING
P_SCHUR_HIGH_MODULATION_POSITIVE_LEADING_TERM_SURVIVES:
  probability: 0.84
  event: independent_paper_check_accepts_15_and_18_without_a_uniform_in_envelope_claim
  fate: PENDING
P_SCHUR_RELATIVE_COMPACTNESS_SURVIVES:
  probability: 0.88
  event: independent_check_accepts_19_and_finite_negative_inertia_on_the_same_completed_moment_null_space
  fate: PENDING
P_SCHUR_SHIFT_TRACE_EXPONENT_THREE_SURVIVES:
  probability: 0.96
  event: independent_check_accepts_25_to_28_with_the_stated_constants_and_projection_assumptions
  fate: PENDING
```
The kernel possibility was stated during this review before the detailed remainder verification; it was not a blind forecast before reading the packet. No probability is retroactively assigned to that exploratory observation.

## 10. One next directive, representations, and dependency epistemics

### Exactly one CODEX DIRECTIVE -- next bounded transaction, not executed here

**Target:** `SCHUR_DYADIC_KERNEL_POSITIVE_EXTENSION_PREFLIGHT`.

First independently verify (5)--(14) against the literal gamma2,t2 source. Required falsifiers are the 2pi normalization, all three resonance families, the absent dyadic term in the archimedean-only finite-kernel case, and the negative finite-rank perturbation of Section 5. A mismatch returns the exact erroneous coefficient or bound; it does not trigger a larger numerical carrier.

After that paper gate, construct the single fixed-cutoff spatial remainder R_c from (7), the quintic chi, and its finite approximants. Return certified e_J and D_J, the origin bound ||R_c||_1, and a lower/upper enclosure for the single scalar function p+hat(R_c) on the intervening compact band determined by (22). This is an analytic-kernel/positive-extension test, not another test-function packet and not a semilocal eigensolve. Record the resulting band and work estimate before authorizing an expensive evaluation; coarse constants may make this particular implementation uneconomical.

**Success:** `SCHUR_SOURCE_POSITIVE_EXTENSION_CERTIFIED`, only if the entire frequency line is covered with a nonnegative lower envelope. Then (13) supplies a whole-class square and (2) the full margin. It still does not discharge the global exhaustion in Section 8.

**Failure:** `SCHUR_KERNEL_IDENTITY_REPAIR_REQUIRED`, `SCHUR_RELATIVE_TAIL_BUDGET_UNRESOLVED`, or `SCHUR_FIXED_EXTENSION_NEGATIVE_NOT_CLASS_REFUTATION`. A negative upper value of this extension rejects only (20) for the fixed chi. A genuine class refutation needs an admissible moment-null test with a negative upper scalar quadratic value. If the extension fails, retain the identity-plus-compact representation (19) rather than rescale the source or clip modes.

| Representation | Exact decision object | Power / cost estimate | Risk |
|---|---|---|---|
| Positive-definite extension of the source logarithmic kernel | p+hat(chi R), with (21)--(22) | 9/10 / 5/10 | The chosen extension can fail although its compression is positive; tail constants may be expensive. |
| Principal-energy relative Schur / compact perturbation | I+K_rel, and (23) with weighted errors | 10/10 / 7/10 | Using the old L2 Gram instead of the principal-energy Gram; an exact relative zero mode needs separate treatment. |
| Full margin with the existing positive correction hierarchy | F plus the actual tested square | 9/10 / 7/10 | Scalar failure does not settle this weaker sufficient interface. |

These are ordinal estimates, not run-time promises. No numerical process, Lean task or Aristotle submission is initiated by this verdict.

**DOWNSTREAM_CONSUMER:** `published_Weil_criterion_on_all_complex_compact_smooth_tests`.
**ACTUAL_CONSUMER_REQUIREMENT:** nonnegativity of the unchanged full Weil form on all those tests.
**ORIGINAL_REQUESTED_OBJECT:** nonnegative signed Schur complement for the fixed scalar-floor class, or a source contraction making it a square.
**ORIGINAL_OBJECT_IS:** `NOT_NECESSARY` for the full-margin or terminal consumer; necessary and sufficient only for the scalar class after a positive head.
**KNOWN_WEAKER_INTERFACES:** full-margin positivity using its extra square; positivity on full exhausting joint test spaces with the pole terms; a scalar positive-extension certificate is sufficient, not necessary, for the compressed scalar form.
**FAILURE_TYPE:** `NO_DERIVATION` for the remaining source sign; `COUNTEREXAMPLE` for reservoir-positivity implying a margin sign, anticommutator automatically being a square, strong-only nonorthogonal pinching, and a finite positive history implying PSD.
**EPISTEMIC_STATUS:** source sign is `RESEARCH_DEBT`. Only those exact abstract inference shapes are refuted, at `THEOREM_SHAPE` scope. No source counterexample or route-family death is asserted.
**NOVELTY_AXIS:** retain the dyadic resonant diagonal and its translated copies before estimating; use their explicit positive energy rather than a uniform L2 gap.
**REOPEN_TRIGGER:** independent acceptance of the new kernel proof followed by a complete lower extension/relative-Schur certificate, or a strictly negative upper value on a genuine source test.
**MINIMAL_MISSING_INEQUALITY:** (24), equivalently I+K_rel>=0 in (19); (20) is the chosen narrower sufficient certificate.
**ZERO_CONSISTENT_DISCRIMINATOR:** the signed relative spectral value at -1 for K_rel, including the exact nullspace if equality persists, or a test upper endpoint below zero. A decreasing positive packet floor is not this discriminator.

## 11. Closeout and publication handoff

What became smaller: the source high-modulation sign is computed; the apparent order-one-half oscillatory multiplier is replaced on this interval by a positive dyadic order-one principal kernel; the residual is relatively compact. The class obstruction is finite negative/zero inertia in a specified energy, not an unbounded collection of unsigned tail modes. This is a new PAPER result, not a completed positivity proof.

What remains: construct a nonnegative full relative operator or positive extension, and separately solve the global class/exhaustion obligations. The eight certified directions do not settle either. What must not recur: the missing 2pi factor, the reversed anticommutator sign, n2 confused with L2-n2, a fitted Weyl law, a raw L2 tail substituted for a relative-energy tail, or deletion of pole constraints under a density claim.

```yaml
META_CLOSEOUT:
  PROGRESS_CLASS: PROOF_PROGRESS
  COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
  ROUTE_SCORE: 5
  iteration:
    target: fixed_moment_null_signed_complement
    status: PROGRESS
    failed_strategy: infer_global_scalar_sign_from_falling_positive_packet_floors
    invariant_learned: translated_dyadic_resonances_produce_cosh_a_over_2_minus_one_times_a_positive_logarithmic_kernel
    remaining_unknown: sign_of_identity_plus_source_relative_compact_remainder
    forbidden_future_move: equate_positive_principal_symbol_or_reservoir_with_the_complete_form
    next_decisive_test: independent_dyadic_kernel_audit_then_fixed_positive_extension_lower_envelope
PUBLICATION_HANDOFF:
  BRANCH: rh_clean
  PATHS_WRITTEN:
    - docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SIGNED_SCHUR_COMPLEMENT_2026-09-07.md
  LEAN_FILES_WRITTEN: []
  LEAN_BLOB_HASHES: []
  LEAN_GATE_COMMANDS: NOT_APPLICABLE_DOCUMENT_ONLY
  EXPECTED_AXIOM_PROFILE: NOT_APPLICABLE_NO_KERNEL_RESULT_CLAIMED
  COMMIT_AND_READBACK_BLOB: supplied_in_delivery_receipt
  RECEIPT_CHANGES_ONLY: publication_status
```

Only this verdict is published. Request bytes, all prior verdicts, predictions in old artifacts, scripts, queue and route state remain untouched. The proofs in this document are PAPER and await independent review. A matching Git blob is not a mathematical verification gate.
