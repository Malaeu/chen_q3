# STATUS: TRY_BOUNDARY_MEAN_CENTERED_SOURCE_RESPONSE
```yaml
OPERATIVE_CLASS: TRY_BOUNDARY_MEAN_CENTERED_SOURCE_RESPONSE
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-10-BOUNDARY
BOUNDARY_ID: GOAL058_SIGNED_BOUNDARY_LOW_ENERGY_COMPARISON
RESULT:
  Q1: PROOF_CANDIDATE_COMPLETE
  Q2: PARTIAL_WITH_PRECISE_REMAINDER
  Q3: PARTIAL_WITH_PRECISE_REMAINDER
  OVERALL: PARTIAL_WITH_PRECISE_REMAINDER
VERIFIER: PAPER
SCOPE: ABSTRACT
ALL_CONTACT_TARGET_SCOPE: COFINAL_FAMILY
ALL_CONTACT_TARGET_VERIFIER: CONDITIONAL
UNIFORM_BOUNDARY_INPUT_VERIFIED: true
SIGNED_SOURCE_COMPARISON_PROVED: false
LOWER_SIGN_PROVED: false
INDEPENDENT_CHECK_OF_NEW_LEMMAS: PENDING
LEAN_VERIFIED: false
PX_RH_CLAIM: NOT_MADE
REQUEST_LOCK:
  REPOSITORY: Malaeu/chen_q3
  BRANCH: rh_clean
  COMMIT: b574857250e2c0e136bb04cfddd906ea1b3aee8f
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_BOUNDARY_2026-09-10.txt
  BLOB: a1c4f3c77013823562e13f86ad7a342e42f16669
  SHA256: 1988f386d36cc16925ddf14d1d67e83c94ab3af1b50a36cd70586a1a5c40a589
  BYTES: 13190
  LINES: 74
  FINAL_LF: true
  ATTACHMENT_HASHES_RECOMPUTED: true
  EXACT_COMMIT_CONNECTOR_BLOB_MATCH: true
SOURCE_BASE: a443424e10a119ded80aca6ddc664b23eaf854fb
BOOTSTRAP_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
CANONICAL_COLLAR:
  COMMIT: d254ce1f1baae6329fc01f20cf2df52a482048ea
  BLOB: 77ba2a24022b5a8993316018db8919e0a15a24a7
  DECLARED_SHA256: 03b9e2ed966dec1d776cf768970992731913f830a087faf0d8f51c35e9cfc51b
  BYTES: 58946
  LINES: 786
  OLD_UNCOMMITTED_COLLAR_SUBSTITUTED: false
SHELF_VERIFICATION:
  PINNED_BLOB_METADATA_MATCHES: 5
  FULL_SHA256_AND_BLOB_RECOMPUTATIONS_MATCH: 3
  FRESH_FULL_HASH_INCOMPLETE: [canonical_COLLAR, CONTACT_independent_check]
  EXTERNAL_V2_STATEMENT_AND_PROOF_READ: true
  EXTERNAL_RAW_HTML_SHA256_RECOMPUTED: false
PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SECOND_EXPRESSION
SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
NEW_PAPER_LEMMAS:
  EXACT_SIGNED_AVERAGED_RESPONSE: section_3_1
  WHOLE_LOW_SPACE_CENTERED_RESPONSE_BOUND: section_3_2
  RANK_TWO_LEADING_RESPONSE_WITH_EXPLICIT_ERROR: section_3_4
  EXACT_CENTERED_AND_TWO_MEAN_ELIMINATION: section_4_2
  KERNEL_OF_CENTERED_MARGIN_EQUALS_ZERO_STRIP_MEANS: section_4_3
FIRST_INCORRECT_ASSERTION_IN_USED_BOUNDARY_INPUT: NONE_FOUND
FIRST_FAILURE:
  Q1: NONE_FOR_STATED_FIXED_A_INPUT_AND_D_DEPENDENT_RELATION
  Q2_INITIAL: no_source_lower_comparison_of_M_with_the_rank_two_leading_response
  Q2_REPAIR: centered_recovery_is_not_proved_strictly_below_M
  Q2_SUBSEQUENT: even_after_centered_strictness_the_exact_two_mean_matrix_needs_a_signed_comparison
  Q3: the_two_signed_source_gates_are_not_discharged_for_every_hypothetical_contact
PREDICTION_FATES:
  P1: CONFIRMED
  P2: CONFIRMED
  P3: CONFIRMED
NEXT_DECISIVE_TEST: CENTERED_BOUNDARY_RECOVERY_RELATIVE_GAP
EXECUTION:
  NUMERICAL_SOURCE_CAMPAIGN: NOT_RUN
  OLD_FINITE_ROWS_RERUN: false
  EXACT_ALGEBRA_CONTROLS: PERFORMED
  LEAN_EDIT: false
  LEAN_GATE: NOT_RUN
  QUEUE_RUNTIME_REGISTRY_EDIT: false
PUBLICATION:
  AUTHORIZED_WRITE_SCOPE: VERDICT_DOC_ONLY
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_BOUNDARY_2026-09-10.md
  COMMIT_STATUS: NOT_COMMITTED
  PUSH_STATUS: NOT_PUSHED
  BLOCKER: no_write_action_exposed_and_git_DNS_resolution_failed
  FINAL_HASH_BYTES_LINES_AND_LOCAL_GIT_BLOB: external_delivery_receipt
HONESTY_STATE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
```

## 0. Decision and evidence boundary

**The leading response can be made explicit without a normalized endpoint limit or a differentiable eigenbasis. It is a rank-at-most-two matrix of signed, averaged source responses. That does not yet prove the signed comparison.** An exact repair then eliminates the centered collar profiles, rather than discarding them. It identifies the first remaining obstruction with a null mode whose integrals over both thin physical strips vanish. Neither the boundary estimate nor the earlier exterior-collar injectivity excludes that event. [ABSTRACT][PAPER]

For each fixed a, with all admissibility conditions below and d decreasing to zero, the new calculation proves
\[
F^*D^{-1}F=\frac d{c_d}\Gamma_d^*\Gamma_d+\mathsf E^{\rm av}_{a,d},
\qquad \|\mathsf E^{\rm av}_{a,d}\|=O_a\!\left(\frac d{\log(1/d)}\right)=o_a(d).
\]
The two rows of Gamma are explicit averages of the complete archimedean, prime and two-pole forcing. This is not an assertion that M/d or either normalized endpoint trace has a limit. Section 4 retains the error exactly before making any further sign claim. [ABSTRACT][PAPER] (fixed a; all sufficiently small d)

**What remains unproved:** strict positivity of the centered low-energy margin, followed by its exact two-mean Schur matrix. No nonzero contact mode is exhibited, and no actual-source negative energy is obtained here. The all-test lower sign remains open. [COFINAL_FAMILY][CONDITIONAL]

### 0.1 Byte locks and actual reading

All repository rows in this table are at SOURCE_BASE. SHA values marked declared are the request's bindings, not claims of a fresh full-file hash computation. Matching GitHub blob metadata is distinguished from independently recomputing that blob from all content bytes.

| Key | Exact repository path | SHA-256 | Git blob | This batch |
|---|---|---|---|---|
| C | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CONTACT_2026-09-10.md` | `3475f7e1d9c11bf2ff259f1d10b967d0fdbbf7c1e68219fcd9c4ab3fcb5dd034` | `dc30c38e5832859e3b84cebaddcf5779545bdd58` | Full local bytes rehashed: 52815 bytes, 729 lines; connector pin matched. READ relevant C1-C8, C19-C21; no repeat of the closed prerequisite campaign. |
| L | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_COLLAR_2026-09-10.md` | `03b9e2ed966dec1d776cf768970992731913f830a087faf0d8f51c35e9cfc51b` | `77ba2a24022b5a8993316018db8919e0a15a24a7` | Canonical pinned passages L4-L29 freshly READ, including overlapping retrieval after truncation. Blob metadata matched; fresh full SHA recomputation NOT completed. |
| I | `docs/routeB_bus/COLLAR_INDEPENDENT_CHECK_2026-09-10.md` | `08a0aedc5e2c32b26dcff0ba94e19432a9ce9770e9bf07cb5d051069359255e4` | `fbac9618c618e23af4b43a1dea7ceddd092a5129` | READ full, including both newest appendices; staged exact text rehashed: 20784 bytes, 156 lines; both hashes match. |
| CI | `docs/routeB_bus/CONTACT_INDEPENDENT_CHECK_2026-09-10.md` | `d3865192de724c857413385eb58b7baa8a0811b0457857c292260c046d451879` | `af682a509363ddcf1f21bcb584b7a4e6f21c6c22` | READ fresh provenance/result scope, lines 1-32. Blob metadata matched; fresh full SHA recomputation NOT completed. Its audit is report evidence, not an axiom. |
| BP | `docs/BATCH_PATTERNS.md` | `cded6dfd5950fd8dd230ad770ff0cf4a50a5bea9b2d5e91601b8eaa76120903b` | `cb63bab5fbff3d39bf63c0b0f081a2264e004f2b` | READ full at the requested outside-routeB path; 11341 bytes, 79 lines; both hashes recomputed and match. |

The attached request was read completely and independently checked for SHA-256, Git blob, bytes, lines and final LF. Its computed blob matches the exact-commit connector response. **Three of five shelf full-hash checks are complete; two are explicitly incomplete.** No mismatch was observed. The older local 54755-byte COLLAR, SHA `41c760d4f4c3cae22b17415adf4734a55210d503f731f15d5497ae34dbc9062a`, is not used as the canonical L-source and is not overwritten.

### 0.2 External import and delivery limits

**[H] READ:** V. Hernández-Santamaría, L. F. López Ríos, A. Saldaña, *Optimal boundary regularity and a Hopf-type lemma for Dirichlet problems involving the logarithmic Laplacian*, arXiv:2401.18033v2, HTML header 03 Jul 2024, `https://arxiv.org/html/2401.18033v2`. Theorem 1.1, (1.2), (1.14)-(1.19), the Theorem 1.1 proof in section 4, and Lemma A.3 with its proof were inspected. The imported implication is: bounded weak solution and bounded right-hand side on an exterior-sphere domain give continuous zero extension and square-root-logarithmic boundary decay. Its proof treats both signs. The source operator's hypotheses are checked in section 2. No Hopf positivity conclusion is imported.

The rendered exact-version text was available. The raw HTML was not acquired and hashed independently, so equality with the parent's 1227643-byte HTML and SHA `2f75d6d6cbb231facf481271b3f673bc2340e3cdde962730f86947e2b37209f3` is **not claimed**. No PDF was used in this batch. The paper's barrier, weak maximum principle and earlier continuity dependencies were not all re-proved here. This is a version-checked theorem import, not a new independent proof of that entire paper.

The GitHub tool discovery returned no usable create/update/commit/push action. Plugin discovery returned the installed GitHub integration, not another write route. A read-only Git connectivity check exited 128 with `Could not resolve host: github.com`. The expected verdict path returned Not Found when checked. This artifact is therefore **NOT_COMMITTED / NOT_PUSHED**, with complete local bytes and an external receipt. No prior session's write receipt is substituted for a current operation.

## 1. Locked source and the exact reduced operator

All operator identities in sections 1-4 carry [ABSTRACT][PAPER] at their displayed hypotheses. The conditional all-contact implications are separately marked. The first-contact hypotheses are used for a contradiction-proof analysis, not claimed to be realized by the source.

Use physical L2 inner products antilinear in the first variable, zero extensions and
\[
\begin{split}
B(f,g)={}&\int_0^\infty\alpha(t)\langle U_tf-f,U_tg-g\rangle_2dt-c_A\langle f,g\rangle_2\\
&-\sum_{n\ge2}w_n\{\langle f,U_{\log n}g\rangle_2+\langle f,U_{-\log n}g\rangle_2\}\\
&+\overline{M_+(f)}M_-(g)+\overline{M_-(f)}M_+(g),\qquad Q[f]=B(f,f),
\end{split}                                                    \tag{BND1}
\]
where alpha, c_A, w_n and M_plus/minus have the request's literal values. The control norm is \(\|f\|_E^2=\int e^{2|x|}|f|^2+\mathcal D[f]\). The window space V_b is its supported logarithmic form domain; it is not H1_0. On each window B is a bounded L2 perturbation of the positive translation form. The already proved C1-C11 give the corresponding closed semibounded A_b, compact resolvent, continuous attained bottom, and positive anchor \(a_0=e^{-20}/2\). The full-source continuity bound is 22. These prerequisites are retained, not inferred from this batch's estimates.

Fix a>0. Let N=ceil(exp(2a))-1, and take 0<d<d_geom(a) exactly as in L4, also d<min(a/2,1/10). Set b=a-d. Under the contact premises require d<a-a0 and L16. L4's integer separation removes only the identically zero prime overlaps inside the two collars; it leaves every nonzero prime channel in the cross operator J. The two collars are (-a,-b) and (b,a), including all four cut boundaries. For the reductions involving A_H and D, assume A_b>0 and L16; these are precisely the hypotheses supplied by the hypothetical contact branch. The boundary-input audit in section 2 does not require positivity of A_b.

Transport their physical L2 space to \(\mathscr H=L^2(0,1)\oplus L^2(0,1)\) by
\[
(U_dw)_\sigma(s)=\sqrt d\,w(\sigma(b+ds)),\qquad \sigma\in\{+1,-1\}.
\]
Let L be the universal zero-extension operator associated to
\[
\mathfrak l[f]=\int_0^1\frac{\|f(\cdot+t)-f\|_2^2}{2t}dt,
\qquad L_2=L\oplus L,
\]
and retain the canonical definitions
\[
\begin{gathered}
c=c_d=2\int_d^\infty\alpha(t)dt-c_A,\quad R=cI+L_2,\quad r_d=c+\log2,\\
U_dC_{a,b}U_d^{-1}=R+E,\quad
\|E\|\le\varepsilon_C=d[4k_a+\alpha(2b)+4\cosh a],\\
P=\mathbf1_{(0,1]}(A_b),\quad A_H=A_b|_{P^\perp}\ge I,\quad J_H=(I-P)J,\\
T_H=U_dJ_H^*A_H^{-1}J_HU_d^{-1},\quad 0\le T_H\le j_a(d)I,\\
\mathscr B=E-T_H,\quad \kappa=\varepsilon_C+j_a(d),\quad
D=R+\mathscr B\ge m_dI,\quad m_d=r_d-\kappa>0,\quad q=\kappa/r_d\le1/2.
\end{gathered}                                                   \tag{BND2}
\]
Here k_a and j_a(d) are the exact source constants from L7-L8. In particular j_a(d)=O_a(1). Bounded perturbations preserve the universal collar operator domain. No high-core mode is omitted from T_H.

Choose an orthonormal basis phi_j of the complete finite-dimensional P-space, with every eigenvalue mu_j in (0,1], all multiplicities and both parity sectors. Put \(\mathsf M=\operatorname{diag}(\mu_j)\), \(u_z=\sum_jz_j\phi_j\), and \(Fz=U_dJ^*u_z\). The maps below act on this entire space at each b. We never differentiate a basis or discard a low branch when the cutoff changes rank.

L20-L23 give, with Y=R^(-1/2)F and T=R^(-1/2)mathscrB R^(-1/2),
\[
\begin{gathered}
\mathsf S=\mathsf M-F^*D^{-1}F,\qquad
\mathsf G_1=Y^*(I-T)Y,\\
\mathsf R_1=Y^*T^2(I+T)^{-1}Y,\quad
0\preceq\mathsf R_1\preceq e_1Y^*Y,\quad e_1=q^2/(1-q),\\
\mathsf S=\mathsf M-\mathsf G_1-\mathsf R_1,
\qquad \mathsf L_1=\mathsf M-\mathsf G_1-e_1Y^*Y\preceq\mathsf S.
\end{gathered}                                                   \tag{BND3}
\]
The positive remainder follows from the scalar identity (1+t)^(-1)-(1-t)=t^2/(1+t) on |t|<1 and self-adjoint functional calculus. Expanding G1 retains the negative E correction and the **positive** high-core recovery F*R^(-1)T_H R^(-1)F. Thus an upper bound on an omitted absolute piece cannot change the signed comparison into a proved theorem.

## 2. Q1: narrow recheck of the uniform boundary input

Inputs: I's two accepted appendices, C1-C8, L17-L19, and the exact external theorem [H] specified in section 0.2. The following local transfer is rederived here. No new source-semigroup positivity, normalized endpoint limit, or cofinal-in-a constant is introduced.

### 2.1 Boundedness of the entire low space without rank or inverse-gap loss

Write A_b=mathcalD_b+B_b, where mathcalD_b is the positive translation-form operator. The finite positive convolution measure
\[
\nu_a=c_A\delta_0+\sum_{2\le n\le N}w_n(\delta_{\log n}+\delta_{-\log n})
+2\cosh(a)\mathbf1_{[-2a,2a]}(t)dt
\]
has mass \(n_a=c_A+2s_a+8a\cosh a\), and dominates |B_bf| pointwise after zero extension. This is an **absolute-value bound**, not positivity of B_b or its semigroup.

For completeness, the positive translation semigroup dominates its supported part. For a nonnegative supported right-hand side compare the whole-line and supported positive resolvents. The positive part of their difference belongs to the supported form domain: the jump-form lattice inequality preserves finite energy and it vanishes outside I_b. Testing the subtracted equations with that positive part gives zero or negative energy for a nonnegative coercive form, so the part is zero. Resolvent iteration gives domination of the semigroups; modulus domination handles complex inputs.

Now use the bounded-perturbation Dyson expansion. Replace each B_b insertion by nu_a convolution and each supported translation semigroup by its whole-line positive counterpart. Convolution operators commute, so the n-th term is bounded by t^n/n! times the whole-line semigroup followed by nu_a to the n-fold convolution power. Summing gives absolute domination by a convolution operator of mass exp(t n_a).

The whole-line multiplier is exp(-t m(xi)), with m>=0 and m(xi)>=log(2|xi|)/2 for |xi|>=1, as in C4/L17. Plancherel and Cauchy-Schwarz imply
\[
\|e^{-t\mathcal D}\|_{2\to\infty}^2
\le\frac{2+2^{1-t}/(t-1)}{2\pi},\quad t>1.
\]
At t=2 this is 5/(4pi). For u in ran P, write u=exp(-2A_b)exp(2A_b)u. Spectral calculus on (0,1] costs at most e^2. Applying the same argument to A_bu gives
\[
\boxed{\|u\|_\infty,\ \|A_bu\|_\infty\le C_a\|u\|_2,
\qquad C_a=e^{2(n_a+1)}\sqrt{5/(4\pi)}.}              \tag{BND4}
\]
This works on the whole projector, not on individual normalized eigenfunctions followed by a dimension factor. The odd reflected-prime obstruction is compatible with this absolute domination.

### 2.2 Domain match and uniform boundary constant

In one dimension [H] uses c_1=1, rho_1=-2gamma. Separate alpha(t)=1/(2t)+k(t) on compact tests. Direct subtraction from its integral formula gives
\[
A_b=\tfrac12L_{\Delta,b}-\log(2\pi)I-K_b-\text{both prime shifts}+\text{both poles},
\quad K_bu(x)=\int_{-b}^bk(|x-y|)u(y)dy.              \tag{BND5}
\]
To check the scalar, the subtraction first gives c0-c_A, with
c0=2 int_0^1 k+2 int_1^infinity alpha+gamma. Substitution z=exp(-2t) yields
2 int_epsilon^infinity alpha=-log(2epsilon)-gamma-psi(1/4)+o(1).
Hence c0=-log2-psi(1/4)=gamma+pi/2+2log2, and c0-c_A=-log(2pi).

Both form norms have the same near-zero 1/|x-y| energy. Away from zero the difference on fixed support is L2 bounded. Therefore their closed form domains agree; their operators differ by a bounded self-adjoint perturbation. This proves the required operator-domain match, not merely equality on an unspecified pointwise class.

Here is why the non-numerical boundary constant can be uniform in b. On J=(-1,1), let
X={v in D(L_Delta,J): v and L_Delta,J v belong to Linfty}, with the sum of the two Linfty norms. It is Banach by closedness of the operator and Linfty convergence implying L2 convergence on J. Theorem 1.1 makes the multiplication map v -> v/sqrt(ell(dist(.,partial J))) defined on every X. This map has closed graph: convergence in X and convergence of the weighted outputs identify the same almost-everywhere limit. The closed graph theorem gives a finite operator bound C_J. Real and imaginary parts can be treated separately with their fixed constant absorbed into C_J.

Let \(\ell(t)=1/|\log\min(t,1/10)|\), and define
\[
\begin{gathered}
V_a=|\log(2\pi)|+2\int_0^{2a}|k(t)|dt+2s_a+4a\cosh a,\\
M_a^{\log}=\max\{|\log(a/2)|,|\log a|\},\\
K_a=\sqrt2 C_JC_a(3+2V_a+2M_a^{\log})
\sqrt{1+M_a^{\log}/\log10}.
\end{gathered}
\]
The bounded potential in (BND5) has Linfty operator norm at most V_a. For v(t)=sqrt(b)u(bt), the exact scaling is
L_Delta,J v=sqrt(b)(L_Delta,b u)(bt)+2log(b)v.
It holds on the weak domain, either by change of variables or [H, Lemma A.3]. Using (BND4) gives ||v||_X<=sqrt(a)C_a(3+2V_a+2M_a^log)||u||_2 for a/2<=b<=a. The elementary maximum-function inequality for log(1/t) and log10 gives ell(t/b)/ell(t)<=1+M_a^log/log10. Consequently
\[
\boxed{|u(x)|\le K_a\|u\|_2\sqrt{\ell(\operatorname{dist}(x,\partial I_b))},
\quad a/2\le b\le a,\quad u\in\operatorname{ran}P_b.} \tag{BND6}
\]
These solutions have continuous zero extensions. This proof supplies neither the limit of u(b-t)/sqrt(ell(t)) nor a derivative with respect to b. The constant C_J, and hence K_a, is finite but not numerically evaluated.

### 2.3 Whole response and complete feedback scale

Let tau_a=min(a/2,1/10) and
\[
B_a^{\rm bd}=K_a/2+C_a[\tfrac12\log(2a/\tau_a)+2ak_a+s_a+4a\cosh a],
\quad \eta_d=4d[K_a^2(\ell_d+1)+(B_a^{\rm bd})^2],\quad \ell_d=\log(1/d).
\]
In either signed source column, integrate its singular part in distance t from the adjacent endpoint. For 0<v<tau_a, splitting at v gives
\[
\int_0^{\tau_a}\frac{dt}{(v+t)\sqrt{\log(1/t)}}
\le\frac1{\sqrt{\log(1/v)}}+2\sqrt{\log(1/v)}
\le1+2\sqrt{\log(1/v)}.
\]
The remaining archimedean kernel, finite prime shifts and two poles are bounded using (BND4). The full sum therefore satisfies
\[
|(Fz)^\sigma(s)|\le\sqrt d\|z\|[K_a\sqrt{\log(1/(ds))}+B_a^{\rm bd}],
\qquad F^*F\preceq\eta_d I.                           \tag{BND7}
\]
Integration uses int_0^1 log(1/s)=1 and bounds the whole vector u_z directly. It introduces no rank factor.

The same scalar integral as in section 2.2 gives r_d=ell_d-gamma-log(pi)+o(1), while kappa=O_a(1). Hence (BND2)-(BND3) imply
\[
F^*D^{-1}F\preceq\eta_d/m_d\,I=O_a(d)I,\qquad
Y^*Y\preceq\eta_d/r_d\,I=O_a(d)I,\qquad
e_1Y^*Y=O_a(d/\ell_d^2)I.                            \tag{BND8}
\]
This completes the narrow audit of the supplied input. The new source relation required by Q1 is proved next; (BND8) alone is not the Q2 signed comparison.

## 3. An actual signed leading response without endpoint limits

This section derives new fixed-a source lemmas. They hold on the complete low projector for every sufficiently small admissible d, not just on a selected eigenfunction. Inputs are (BND4)-(BND8), the literal L18 columns and the universal collar form L11. No new external theorem is used.

### 3.1 Exact averaged source rows

Let \(\iota:\mathbb C^2\to\mathscr H\) send (z_plus,z_minus) to the two constant profiles. It is an isometry. Set \(\Pi=\iota\iota^*\), \(\Pi_\circ=I-\Pi\), and define
\[
\Gamma_d=d^{-1/2}\iota^*F,\qquad F_\circ=\Pi_\circ F,
\qquad F=\sqrt d\,\iota\Gamma_d+F_\circ,\quad\iota^*F_\circ=0. \tag{BND9}
\]
The two rows of Gamma are **averaged exterior forcing**, not assumed boundary traces of u. Here is their literal source formula. For sigma=+1 or -1 put
\[
\begin{gathered}
\bar\alpha_d(t)=\frac1d\int_0^d\alpha(t+v)dv,\qquad
\bar u_{n,d}^\sigma=\frac1d\int_0^d u(\sigma(b+v-\log n))dv,\\
p_\pm^\sigma(b,d)=e^{\pm\sigma b/2}\int_0^1e^{\pm\sigma ds/2}ds.
\end{gathered}
\]
For every u=u_z in the low space, direct integration of L18 gives
\[
\boxed{\begin{split}
(\Gamma_d z)_\sigma={}&-\int_0^{2b}\bar\alpha_d(t)u(\sigma(b-t))dt
-\sum_{n=2}^{N}w_n\bar u_{n,d}^\sigma\\
&+p_+^\sigma(b,d)M_-(u)+p_-^\sigma(b,d)M_+(u).
\end{split}}                                                       \tag{BND10}
\]
All averages are finite. For the singular part, the double integral of 1/(t+v) over a bounded positive rectangle is finite; boundedness of u justifies Fubini. The regular kernel is bounded, the prime sum finite, and the pole moments finite. Thus no interchange requires a pointwise equation at an endpoint. The formula remains valid with the continuous zero representative provided by (BND6).

Reflection of the source interchanges the two output rows. On an even input they agree; on an odd input they differ by sign. This identifies at most one mean channel per parity, but it neither restricts the dimension of an eigenspace nor discards either sector. The products Gamma*Gamma are formed only after summing all signed terms in (BND10), including their mixed products.

### 3.2 The centered response is smaller on the entire low space

Define explicit fixed-a constants
\[
O_a=4ak_a+2s_a+8a\cosh a,
\qquad \omega_a=2C_a^2(O_a^2+O_a+1/2).
\]
Then
\[
\boxed{F_\circ^*F_\circ\preceq d\omega_a I.}           \tag{BND11}
\]
**Proof.** Write \(r_\sigma(s)=(Fz)_\sigma(s)/\sqrt d\). Compare it with r_sigma(1), which is evaluated at positive distance d from the core; the latter evaluation is well-defined. For its singular archimedean term,
\[
0\le\int_0^{2b}\left(\frac1{t+ds}-\frac1{t+d}\right)dt
=\log(1/s)+\log\frac{2b+ds}{2b+d}\le\log(1/s).
\]
Its contribution to the difference has modulus at most C_a||z|| log(1/s)/2. The two regular-kernel integrals together cost at most 4ak_a C_a||z||. The two prime sums cost at most 2s_a C_a||z||. Each complete pole response has modulus at most 4a cosh(a) C_a||z||, so their difference costs at most 8a cosh(a) C_a||z||. These bounds keep both poles and all prime channels, irrespective of the input's phase or parity. Therefore
\[
|r_\sigma(s)-r_\sigma(1)|
\le C_a\|z\|[O_a+\tfrac12\log(1/s)].
\]
The constant projection is the best L2 approximation by constants. Its squared error is consequently at most the squared distance to r_sigma(1). Integrate, use int log(1/s)=1 and int log(1/s)^2=2, sum the two channels and multiply by d. This gives exactly (BND11). The estimate is for u_z as a whole; no sum of separate eigenfunction bounds is introduced. QED.

The estimate does not say ||J|| tends to zero. Its domain is the bounded complete low source space, followed by removal of the two mean profiles. The singular corner and reflected prime term remain in the exact operator and in omega_a.

### 3.3 Only the two constant profiles admit the required scalar inverse approximation

The universal form has the exact decomposition
\[
\mathfrak l[f]=\tfrac12\int_{0<x<y<1}\frac{|f(y)-f(x)|^2}{y-x}\,dxdy
+\int_0^1 V(s)|f(s)|^2ds,\qquad V(s)=-\tfrac12\log[s(1-s)].
\]
The constant profile 1 has finite form energy. Polarizing against it cancels the regional term and gives L1=V in L2, hence 1 is in the **operator** domain. Direct elementary integration gives
\[
\langle1,L1\rangle=\int_0^1V=1,
\qquad \|L1\|_2^2=2-\pi^2/12<2.
\]
For the second identity one may integrate the convergent power series for log(1-s) against log(s): int log(s)log(1-s)=2-pi^2/6. Thus
\[
\iota^*L_2\iota=I_2,\qquad \|L_2\iota\|\le\sqrt2.   \tag{BND12}
\]
In particular the constant-channel diagonal is c+1, **not** c+log2. The latter is only a lower bound for the whole universal operator.

Since mathscrB is bounded, constants also belong to D(D). Applying D^(-1) to D iota=c iota+(L2+mathscrB)iota yields the exact restricted identity
\[
D^{-1}\iota-c^{-1}\iota
=-c^{-1}D^{-1}(L_2+\mathscr B)\iota,
\qquad
\|D^{-1}\iota-c^{-1}\iota\|
\le\delta_d^{\rm inv}:=\frac{\sqrt2+\kappa}{c\,m_d}.  \tag{BND13}
\]
This is O_a(ell_d^(-2)). It is a statement on two fixed profiles with a proved graph bound. It makes **no** assertion that ||I-cD^(-1)|| tends to zero on the infinite-dimensional collar. The latter relative scalarization is still prohibited by canonical L14.

### 3.4 Full leading response, signed error and leading cancellation

Define the exact Hermitian matrix
\[
\mathsf E^{\rm av}_{a,d}=F^*D^{-1}F-\frac d c\Gamma_d^*\Gamma_d.
\]
Equations (BND7), (BND9), (BND11) and (BND13) prove
\[
\boxed{\begin{gathered}
\|\mathsf E^{\rm av}_{a,d}\|\le\varepsilon^{\rm av}_{a,d},\\
\varepsilon^{\rm av}_{a,d}
=\eta_d\delta_d^{\rm inv}
+2\sqrt{\eta_d d\omega_a}\,\delta_d^{\rm inv}
+\frac{d\omega_a}{m_d}
=O_a(d/\ell_d).
\end{gathered}}                                                   \tag{BND14}
\]
**Proof.** Expand the quadratic response using F=Pi F+F_circle. The mean-mean difference from c^(-1)(Pi F)*(Pi F) is bounded by eta_d delta_inv. For the two mixed terms subtract c^(-1)iota inside D^(-1)iota: the subtracted term pairs to zero with F_circle. Their combined norm is at most 2 sqrt(eta_d d omega_a) delta_inv. The centered-centered response is positive and at most d omega_a/m_d. These are all terms of the exact expansion, proving the bound in matrix order as well as norm. Since eta_d=O(d ell_d), c and m_d are asymptotic to ell_d, the stated rate follows. QED.

This identifies an actual rank-at-most-two leading response, with an explicit whole-space error. It does not merely assign another upper scale to the old norm. Its coefficients are (BND10), including source signs and all mixed products. No convergence assumption about Gamma_d/sqrt(ell_d) is needed.

The **signed low-energy relations** now read
\[
\boxed{\begin{split}
\mathsf S&=\mathsf M-\frac d c\Gamma_d^*\Gamma_d-\mathsf E^{\rm av}_{a,d},\\
\mathsf M-\mathsf G_1
&=\mathsf M-\frac d c\Gamma_d^*\Gamma_d-\mathsf E^{\rm av}_{a,d}+\mathsf R_1.
\end{split}}                                                       \tag{BND15}
\]
Every term is an explicitly defined matrix, not an asserted limiting coefficient.

At a hypothetical contact choose any unit vector z_d in ker S, which exists by canonical L20-L21. Then
\[
\left|z_d^*\left(\mathsf M-\frac d c\Gamma_d^*\Gamma_d\right)z_d\right|
\le\varepsilon^{\rm av}_{a,d}=o_a(d),
\qquad
z_d^*(\mathsf M-\mathsf G_1)z_d=z_d^*\mathsf R_1z_d.    \tag{BND16}
\]
This is a conditional **leading cancellation law for the actual source equality system**. Its leading rows have just been identified without a branch limit. It is not a contact witness and not a refutation of a contradiction-proof target. It shows precisely what an attempted strict order-d lower margin would have to contradict using an additional signed source fact.

**Q1 result:** the supplied fixed-a input survives the narrow recheck, and (BND9)-(BND16) provide the requested actual d-dependent leading relation. FIRST_FAILURE Q1: none for these claims. Existence of normalized endpoint limits, Hadamard differentiability and a limit of M/d are deliberately not claimed.

## 4. Q2: the attempted comparison and its concrete repair

### 4.1 First attempt: an order-d lower gap, and why it is unpaid

An unpaid sufficient attempted source estimate [COFINAL_FAMILY][CONDITIONAL] is
\[
\mathsf M-\frac d c\Gamma_d^*\Gamma_d\succeq\gamma_a d I,
\qquad \gamma_a>0,                                  \tag{BND17}
\]
for each hypothetical contact a, with one fixed gamma_a>0 and for every sufficiently small admissible d. This is a sufficient, not necessary, target. Equations (BND14), (BND15) and the complete e1Y*Y=o(d) error would then allow a d for which the total error is smaller than gamma_a d and L1 is positive. But **no such signed estimate has been derived**. Equation (BND16) records the cancellation it must overcome. A bound on Gamma alone supplies no lower bound on M along its active rows.

This is the first exact failed proof step, not a claim that the theta target is false. The packet's scalar control already rules out the generic inference from the scales: A=d, C=ell_d, J=t sqrt(d ell_d) gives recovery=d t^2 and S=d(1-t^2). At t=1, exact equality persists. With q=1/ell_d and d=e^(-4), e1=1/12 and L1=-d/12 although S=0. Our formulas preserve that result; they do not declare a negative source energy from the sufficient envelope.

A normalized endpoint/Hadamard approach would additionally need the existence and transport of trace coefficients before differentiating. Those facts are not supplied by (BND6). Rather than assuming them or increasing feedback order, the following repair eliminates the entire centered response exactly.

### 4.2 Exact elimination of centered collar profiles

Let \(\mathscr H_\circ=\ker\iota^*\). The projection Pi_circle is bounded in the collar form norm: constants have finite form energy, and their coefficients are bounded L2 functionals. Thus the restriction of D's closed form to H_circle is closed and densely defined there. Its Friedrichs operator D_circle satisfies D_circle>=m_d I.

Constants are in D(D) by (BND12), so the cross map
\[
W_d=\Pi_\circ D\iota=\Pi_\circ(L_2+\mathscr B)\iota,
\qquad \|W_d\|\le v_d:=\sqrt2+\kappa
\]
is a bounded map from C2 to H_circle. The exact operator on C2 direct-sum H_circle therefore has finite/centered blocks
\[
D=\begin{pmatrix}D_{00}&W_d^*\\ W_d&D_\circ\end{pmatrix},
\qquad D_{00}=(c+1)I_2+\iota^*\mathscr B\iota.
\]
This follows by polarizing its form; bounded cross terms give the same block-operator domain. Define
\[
\begin{gathered}
\mathsf K_e=D_{00}-W_d^*D_\circ^{-1}W_d,\qquad
\mathsf J_e=\sqrt d\,\Gamma_d-W_d^*D_\circ^{-1}F_\circ,\\
\mathsf N_\circ=F_\circ^*D_\circ^{-1}F_\circ,\qquad
\mathsf B_\ell=\mathsf M-\mathsf N_\circ.
\end{gathered}                                                    \tag{BND18}
\]
The symbol B_ell denotes a finite **centered low-energy margin**, not the original sesquilinear form B. Neither it nor its inverse is assumed positive here.

The positive two-mean operator satisfies K_e>=m_d I_2: minimizing the D-energy over the centered component for fixed mean coefficient xi gives xi*K_e xi; D>=m_d and ||iota xi+h||^2=||xi||^2+||h||^2 give the inequality. Thus its inverse is legitimate without a source-sign hypothesis beyond the already proved positivity of D.

Solving the centered block first, or completing its positive form square, proves the exact identities
\[
\boxed{F^*D^{-1}F=\mathsf N_\circ+\mathsf J_e^*\mathsf K_e^{-1}\mathsf J_e,
\qquad
\mathsf S=\mathsf B_\ell-\mathsf J_e^*\mathsf K_e^{-1}\mathsf J_e.} \tag{BND19}
\]
For example, for a right-hand side (f0,f_circle), the centered component of the solution is D_circle^(-1)(f_circle-W_d xi); the mean equation is K_e xi=f0-W_d*D_circle^(-1)f_circle. Pairing the solution with the same right-hand side gives exactly (BND19). This derivation also proves the domain validity of the elimination for arbitrary L2 data.

There is no unretained operator tail in (BND19). D_circle still contains the **entire** T_H, E, and universal logarithmic response. No coefficient has been numerically evaluated or certified here. Exact retention is not the same as having proved its needed comparison with M.

The already proved estimates give explicit bounds on the repaired objects:
\[
\begin{gathered}
0\preceq\mathsf N_\circ\preceq\frac{d\omega_a}{m_d}I=O_a(d/\ell_d)I,\\
\|\mathsf J_e-\sqrt d\Gamma_d\|\le\frac{v_d\sqrt{d\omega_a}}{m_d},\qquad
\|\mathsf K_e-(c+1)I_2\|\le\kappa+\frac{v_d^2}{m_d}.
\end{gathered}                                                     \tag{BND20}
\]
Thus the centered sector is subleading in absolute size, but its subtraction from M is kept **exactly**. It need not be subleading relative to every mu_j. Both signs of the high-core and pole feedback continue to enter every repaired object through D.

### 4.3 The new first failure is a precise source-measurement problem

At a hypothetical contact, S is nonnegative, so (BND19) implies B_ell>=0 and
\[
\ker\mathsf B_\ell=\ker\mathsf S\cap\ker\mathsf J_e.  \tag{BND21}
\]
This follows from the sum of the two nonnegative matrices S and J_e*K_e^(-1)J_e, not from a claim about a sign-definite eigenfunction.

There is an exact physical interpretation. The L21 reconstruction maps z in ker S to
\[
w=-U_d^{-1}D^{-1}Fz,\quad x_H=-A_H^{-1}J_Hw,
\quad v=u_z+x_H+w\in\ker A_a.
\]
Conversely every contact null vector has this decomposition, since both positive squares in L20 must vanish. A null vector with zero low projection would vanish entirely. The correspondence is therefore a linear bijection.

The solved mean block gives
\[
\iota^*U_dw=-\mathsf K_e^{-1}\mathsf J_e z
=\frac1{\sqrt d}
\begin{pmatrix}\int_b^a v(x)dx\\ \int_{-a}^{-b}v(x)dx\end{pmatrix}. \tag{BND22}
\]
The factor 1/sqrt(d) follows from the unitary physical rescaling. It must not be replaced by 1/d or omitted.

Combining (BND21)-(BND22) proves the source identity
\[
\boxed{\ker\mathsf B_\ell\ \simeq
\left\{v\in\ker A_a:\ \int_b^av=0,\quad\int_{-a}^{-b}v=0\right\}.} \tag{BND23}
\]
In particular, at contact, B_ell is strictly positive if and only if the two strip-integral functionals are injective on the full contact kernel. These are **ordinary physical strip integrals**, not limiting logarithmic traces and not the averaged forcing Gamma. Their relation to Gamma includes the exact centered feedback in J_e.

This identifies the repaired mechanism's first missing source statement [COFINAL_FAMILY][CONDITIONAL]:
\[
\begin{gathered}
\text{for each hypothetical first-contact }a,\text{ choose one admissible }d:\\
\forall v\in\ker A_a,\quad
\int_{a-d}^a v=\int_{-a}^{-a+d}v=0\quad\Longrightarrow\quad v=0.
\end{gathered}                                                     \tag{BND24}
\]
**(BND24) is not proved.** Continuous zero endpoint values do not imply it. Vanishing integrals do not imply vanishing functions on the strips, so CONTACT's exterior-collar injectivity cannot be substituted. Automatic radical-tail orthogonality supplies no additional equation for these integrals.

The rank requirement is visible rather than hidden: injectivity into C2 would force dim ker A_a<=2. Reflection would further allow at most one dimension in each parity sector. These are consequences of the missing statement, **not assumptions made about the actual kernel**. Any proof using a single positive ground state would have to pay those hypotheses separately. Our calculation uses neither simplicity nor positivity preservation.

### 4.4 Even the repaired centered gate is not the final signed comparison

If B_ell is independently proved positive, one can then define the two-by-two Hermitian matrix
\[
\mathsf E_e=\mathsf K_e-\mathsf J_e\mathsf B_\ell^{-1}\mathsf J_e^*.
\]
Completing the two possible squares in the block matrix with diagonals B_ell and K_e proves
\[
\boxed{\mathsf S\succ0\quad\Longleftrightarrow\quad
\mathsf B_\ell\succ0\ \text{ and }\ \mathsf E_e\succ0.} \tag{BND25}
\]
For the forward implication B_ell=S+J_e*K_e^(-1)J_e>0, and the second Schur complement is positive. The converse is the reverse congruence. If r=0, L20's positive squares already exclude contact; otherwise all r low directions remain present in B_ell.

At contact, when B_ell happens to be positive, E_e is nonnegative and singular. For a nonzero z in ker S, xi=K_e^(-1)J_e z is nonzero and E_e xi=0. Thus the small matrix must retain an equality branch. A proof of (BND24) alone would only reach this final signed branch; it would not prove contact exclusion.

**FIRST_FAILURE Q2 after the concrete repair:** no source estimate proves
\(\mathsf N_\circ\prec\mathsf M\), equivalently (BND24) at contact. The subsequent strict comparison E_e>0 is also unpaid. The missing entries are the actual products of centered full-source columns through D_circle^(-1), compared with the actual mu_j. No inverse of B_ell is used before this gap is discharged.

## 5. Adversarial controls and what they do not prove

All exact controls in this section are [ABSTRACT][PAPER]. They test the stated inference; they are not arithmetic first-contact examples.

### 5.1 Required scaled control

For 0<d<exp(-3), ell_d=log(1/d), A=d, C=ell_d and J=t sqrt(d ell_d), direct completion gives recovery=d t^2 and S=d(1-t^2). The form is positive for |t|<1, singular at t=1 and indefinite for |t|>1. Set R=C, E=T_H=0, Y*Y=d t^2 and conservative q=1/ell_d. At d=exp(-4), t=1, e1=1/12 and L1=-d/12. The exact S stays zero. Our signed identities return that equality, not a negative-energy or positive-gap verdict.

The source properties proved in section 3 are absent from this control: they are the literal alpha-averaged rows, the source boundedness that controls their centered oscillation, and the fixed-profile universal graph identity L1=V. They give the new representation. **They have not been shown to force the strict source inequality.** There is no proved source property in this submission that may honestly be said to eliminate the control's equality and then automatically eliminate actual contact.

### 5.2 A control aimed specifically at the concrete repair

Take a scalar low space, a three-dimensional collar, and
\[
\mathsf M=d/\ell_d,\qquad D=\ell_d I_3,\qquad
\iota(z_+,z_-)=(z_+,z_-,0),\qquad F=\sqrt d\,e_3.
\]
Then Gamma=0, F_circle=F, W_d=0, K_e=ell_d I_2, J_e=0, and
\[
\mathsf N_\circ=d/\ell_d=\mathsf M,\qquad
\mathsf B_\ell=0,\qquad\mathsf S=0.                  \tag{BND26}
\]
Here the centered recovery is o(d) and F_circle*F_circle=d, exactly compatible with the new absolute scales. Nevertheless it consumes the entire low energy. The proposed rate-only conclusion B_ell>=M/2 has exact success margin
\[
0-\frac{d}{2\ell_d}=-\frac{d}{2\ell_d}<0.
\]
This is a strict negative upper envelope for that **abstract theorem shape**. It kills the inference that an o(d) centered response is necessarily negligible relative to M. It does not kill the true source comparison. The example has no alpha kernel, von Mangoldt shifts, pole structure, universal unbounded collar operator or fixed-source window evolution. Those omissions are why it is an algebraic control, not a theta-source counterexample.

### 5.3 Reflected prime and endpoint controls

The full rows (BND10) and F_circle retain the reflected n=2 contribution of the odd lift. No semigroup-positivity assumption about A_b or D is used. The absolute Dirichlet-semigroup domination in section 2 concerns the independent positive translation form, followed by an absolute perturbation series. It does not contradict the already checked positive odd off-diagonal pairing or imply negative energy from that pairing.

Dropping the +F*R^(-1)T_H R^(-1)F term in G1 would undercount recovery. Replacing L1=V by L1=0 would lose the exact c+1 diagonal in (BND18). Replacing the two strip integrals in (BND23) by point values would be especially destructive: all continuous zero-extended low modes have zero endpoint values, whereas the strip measurements can be nonzero. Each of these alterations changes a displayed identity and would let a false simplification pass.

An exact rational three-by-three block with D=[[5,1,1],[1,6,2],[1,2,7]] and F=[[1,2],[2,-1],[3,1]] independently reproduced (BND19) by symbolic inversion. The packet e1=1/12 and the centered control were also checked symbolically. These tests supplement the all-domain proofs; they do not evaluate the source matrices or replace any quantifier.

## 6. Q3: exact whole-source transfer, with both unpaid gates visible

The source lemmas above are [ABSTRACT][PAPER]. This section's all-contact conclusion is [COFINAL_FAMILY][CONDITIONAL] because its two signed premises remain unproved.

Suppose one independently establishes, for every a>a0 satisfying the first-contact premises, one d with all L4/L16 conditions, d<min(a-a0,a/2,1/10), and
\[
\mathsf B_\ell\succ0,\qquad
\mathsf K_e-\mathsf J_e\mathsf B_\ell^{-1}\mathsf J_e^*\succ0. \tag{BND27}
\]
By (BND25), S>0. The original source energy for v=u_z+x_H+w is exactly
\[
Q[v]=Q_H[x_H+A_H^{-1}J_Hw]
+\|D^{1/2}(U_dw+D^{-1}Fz)\|_2^2+z^*\mathsf S z.
\]
The physical change from (z,x_H,w) to the three displayed coordinates is bounded and has a bounded triangular inverse. The two infinite-dimensional positive blocks have floors 1 and m_d; the finite positive matrix S has a strictly positive smallest eigenvalue. Thus there is a positive physical L2 lower bound on the full window. It contradicts lambda_a=0. No component is discarded, including when it is odd or belongs to a multiple low eigenvalue.

The existing positive anchor, continuity and attainment now give the terminal contradiction: a nonpositive later window would have a first zero window. That window is excluded by the preceding argument. Each complex compact smooth f belongs to some sufficiently large V_a, so Q[f]>=0. This is exactly the all-test sign required by the published Weil consumer; no norm rescaling or pole-null restriction occurs in the passage.

**This proves the implication from (BND27), not (BND27).** Source kernel exclusion and unconditional lower sign are therefore not claimed. The exact two-mean repair is an alternative to proving the particular sufficient one-feedback envelope L29. It does not silently declare that envelope positive or remove its complete remainder.

| Supplier | Domain, quantifiers and normalization | Input/output and exact proof locator | Status |
|---|---|---|---|
| Fixed-window analytic prerequisites | Every physical complex V_a; a0=e^(-20)/2 | C1-C11: closed form, compact resolvent, attained continuous bottom, positive start | Retained paper results; not rerun. [ABSTRACT][PAPER] |
| Uniform low-space boundary input | Fixed a>0, a/2<=b<=a, every u in ran 1_(0,1](A_b); physical L2 | C/L17 plus [H], rechecked in (BND4)-(BND7), give C_a,K_a and eta_d | Verified import transfer and local derivation; no numerical K_a. [ABSTRACT][PAPER] |
| Full source coupling and high-core elimination | Every admissible split, all low multiplicities and both collars | Canonical L4-L23 and (BND1)-(BND3): exact F,D,M,S,R1 | Exact at stated positivity hypotheses. [ABSTRACT][PAPER] |
| Averaged leading response | Same parameters, every coefficient vector z | Literal (BND10), centered bound (BND11), restricted inverse (BND13) give (BND14)-(BND16) | New paper lemmas; no endpoint limit. [ABSTRACT][PAPER] |
| Centered-profile elimination | H_circle=ker iota*, same zero-extension domain | (BND18)-(BND23): exact centered recovery and physical strip-mean kernel identity | New paper lemmas; no inverse of B_ell assumed. [ABSTRACT][PAPER] |
| Centered strictness | Every hypothetical contact, at least one admissible d | N_circle strictly below M, or equivalently strip-mean injectivity on the contact kernel | FIRST unpaid source gate. [COFINAL_FAMILY][CONDITIONAL] |
| Remaining two-mean strictness | Same d and only after B_ell>0 | E_e>0 in (BND25) | SECOND unpaid signed gate. [COFINAL_FAMILY][CONDITIONAL] |
| All-test lower sign | Every complex compact smooth f | (BND27), L20 and first-contact contradiction | Implication proved; inputs unpaid. [COFINAL_FAMILY][CONDITIONAL] |

FIRST_FAILURE Q3: no unconditional proof supplies the two signs in (BND27) at the required all-contact quantifiers. There are no witnesses d(a) or positive margin constants for that statement in this submission. There is no omission of a numerical tail masquerading as that gap: the remaining issue is the full signed source comparison itself.

## 7. Route map, strongest attack and dependency epistemics

| Representation | What it preserves; what remains unpaid | Estimated kill-power / proof cost | Disposition |
|---|---|---|---|
| **Chosen: exact averaged/centered source response** | Full source, physical norms, four boundaries, both parities and all low modes. Produces explicit leading rows and retains centered feedback exactly. | 9/10 / 6/10 | New lemmas proved; relative centered gate and two-mean sign unpaid. |
| **Alternative: normalized boundary trace and shape variation** | Could target a signed variation of low energies, but would need trace existence, basis-free cluster transport and a valid shape identity. | 8/10 / 8/10 | Candidate only; those premises are not supplied by the boundary bound. |
| **Rejected inference: absolute smallness is relative smallness** | Loses the relationship to every mu_j, even with complete o(d) error. | 10/10 / 1/10 against the inference | Exact negative success margin in (BND26); no theta-source refutation. |

The scores rank proposed proof work, not probabilities, numerical evidence or authorization for a source computation. No precision, degree, feedback-order or window escalation is requested.

The strongest objection to the chosen reduction is substantive: **two mean measurements need not see a multiple or sign-changing contact kernel**. That objection is accepted and becomes the exact equivalence (BND23), rather than a hidden assumption. Small or zero strip integrals do not imply the two strips vanish. If B_ell is singular, the reduction preserves the corresponding local kernel rather than incorrectly invoking exterior continuation. Even after that branch is excluded, the actual two-mean recovery still needs its sign comparison.

```yaml
K8A:
  DOWNSTREAM_CONSUMER: published_Weil_criterion_on_all_complex_compact_smooth_tests
  ACTUAL_CONSUMER_REQUIREMENT: Q_nonnegative_on_all_complex_compact_smooth_tests
  ORIGINAL_REQUESTED_OBJECT: all_contact_strict_one_feedback_boundary_margin
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACES:
    - exact_source_kernel_exclusion_at_first_contact
    - exact_S_positive_without_the_chosen_one_feedback_majorant
    - direct_all_test_lower_sign_or_a_cofinal_lower_envelope_tending_to_zero
  CHOSEN_INTERFACE_IMPLICATION: BND27_to_positive_S_to_no_first_contact_to_all_test_sign
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: signed_averaged_source_rows_and_exact_centered_kernel_measurement_identity
  REOPEN_TRIGGER: source_relative_centered_recovery_gap_then_full_two_mean_signed_comparison
SCOPED_REFUTATION:
  CLAIM: an_o_d_centered_recovery_is_automatically_negligible_relative_to_every_low_energy
  KILL_SCOPE: THEOREM_SHAPE
  KILL_EVIDENCE_KIND: exact_negative_upper_envelope_for_the_claimed_half_energy_margin
  EVIDENCE: BND26_in_this_verdict
  SUCCESS_MARGIN: minus_d_over_two_log_one_over_d
  FAILURE_TYPE: COUNTEREXAMPLE
  EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
  ACTUAL_SOURCE_COUNTEREXAMPLE: false
CLOSES:
  - narrow_uniform_boundary_import_and_source_transfer_recheck
  - exact_d_dependent_leading_signed_source_response_representation
  - abstract_absolute_to_relative_negligibility_inference
OPENS: []
CARRIES_OPEN:
  - full_source_signed_boundary_low_energy_comparison
  - first_contact_exclusion
  - all_test_lower_sign
```

The two unpaid gates are an exact factorization of the previous comparison, not two newly accepted premises or new route obligations. They are required only by this chosen representation. Their use is justified by (BND19)-(BND25), not by a claim that every possible proof must pass through two means. No route-family impossibility is asserted.

## 8. One next_decisive_test, frozen predictions and handoff

### 8.1 CENTERED_BOUNDARY_RECOVERY_RELATIVE_GAP

**One analytical test only.** The target is [COFINAL_FAMILY][CONDITIONAL]. Work on the actual full source at every hypothetical first-contact a, with exactly the complete spectral projector (0,1]. Seek one admissible d and one delta(a,d)>0 such that
\[
\boxed{
F_\circ^*D_\circ^{-1}F_\circ\preceq(1-\delta(a,d))\mathsf M
\quad\text{for every complex low coefficient vector}.}             \tag{BND28}
\]
All constants can depend on this a,d; no uniform positive spectral gap is requested. The exact terminal observable is
\[
\vartheta_{a,d}
=\lambda_{\min}\!\left(
I-\mathsf M^{-1/2}F_\circ^*D_\circ^{-1}F_\circ\mathsf M^{-1/2}\right).
\]
M is invertible because b<a and the core is positive. Defining this finite relative normalization does not estimate an operator by 1/mu_min. The task is a signed, source-coupled inequality before any worst-eigenvalue bound.

For explicit source data, F_circle z is exactly the pair of functions
\[
\sqrt d\left[
-\int_0^{2b}\bigl(\alpha(t+ds)-\bar\alpha_d(t)\bigr)u_z(\sigma(b-t))dt
-\sum_{n=2}^{N}w_n\bigl(u_z(\sigma(b+ds-\log n))-\bar u_{n,d}^\sigma\bigr)
\right.
\]
\[
\left.
+\bigl(e^{\sigma(b+ds)/2}-p_+^\sigma\bigr)M_-(u_z)
+\bigl(e^{-\sigma(b+ds)/2}-p_-^\sigma\bigr)M_+(u_z)
\right],\qquad\sigma\in\{+1,-1\}.                                \tag{BND29}
\]
The centered profiles must be combined with their signs before applying the exact D_circle inverse. Formula (BND29) is the new source functional at the first failure, not a replacement prime-only form.

**Success condition:** a proof of (BND28) with the all-contact quantifiers, or a clearly scoped finite-window theorem with the complete inverse retained and all inequalities certified. This closes only the centered gate. It does not certify E_e>0 or lower sign.

**Equivalent source route for the same test:** prove injectivity of the two ordinary strip-integral functionals on ker A_a, at one admissible d, as in (BND24). This is the same terminal gate by (BND23), not a second test. It must cover both parity sectors and all kernel multiplicities.

**Stop condition:** stop this subattempt if it produces only d omega_a/(m_d mu_min), an o(d) estimate without a relative comparison, a sign-definite-ground-state assumption, or the unproved assertion that zero strip integrals imply zero strips. Record `CENTERED_SOURCE_RELATIVE_GAP_UNRESOLVED`; do not increase feedback order or precision. A zero-consistent enclosure needs the exact kernel/strip-mean discriminator, not a smaller floating display. The algebraic controls in section 5 must continue to return equality.

This directive is for source-paper proof construction and independent checking, not authorization for a new numerical campaign or for Lean, queue or state edits. It does not ask to refine any closed finite row.

### 8.2 Frozen prediction scores

| Prediction frozen in the request | Fate | Exact evidence and limit |
|---|---|---|
| P1, p=0.90: uniform boundary/full-response input survives at fixed a | CONFIRMED | (BND4)-(BND8) recheck domain, full-projector bounds, scaling and the complete feedback scale. [H] is a version-checked import, not a fresh proof of all its dependencies. The incomplete byte checks remain separately disclosed. |
| P2, p=0.95: rates and o(d) error alone do not exclude equality | CONFIRMED | The required scaled control returns S=0, L1=-d/12. (BND26) additionally defeats the relative centered-smallness inference. |
| P3, p=0.80: partial result with a new source relation or exact mechanism refutation | CONFIRMED | New (BND10)-(BND16) identify actual leading source rows; (BND18)-(BND23) give exact centered repair and its physical first failure. Neither gate in (BND27) is proved. |

The scores concern this submitted paper derivation. Independent verification of the new lemmas is pending. No old numerical prediction is rescored and no probability is used as a premise or stopping rule.

### 8.3 Closeout and verification handoff

What became more explicit: the O(d) recovery now has a literal two-row leading source matrix and a proved o(d) error. A complete centered elimination identifies exactly which null modes would escape those two channels. What did not become smaller in logical strength: the all-test sign still needs an independent signed source comparison.

What is refuted: only the abstract inference from an absolute o(d) centered response to relative smallness against M. What must not recur: scalarizing the whole universal inverse, turning zero endpoint values into zero strips, dropping the reflected prime or high-core feedback, or reading a nonpositive sufficient lower envelope as negative source energy.

```yaml
iteration:
  target: GOAL058_SIGNED_BOUNDARY_LOW_ENERGY_COMPARISON
  status: OPEN
  progress_class: REPRESENTATION_PROGRESS
  cognitive_operator_used: REPRESENTATION_SHIFT
  failed_strategy: infer_a_strict_order_d_gap_from_absolute_boundary_and_feedback_scales
  new_gap_name: centered_full_source_recovery_relative_to_actual_low_energies
  invariant_learned: leading_rank_two_does_not_make_centered_feedback_relatively_negligible
  forbidden_future_move: assume_strip_means_detect_the_full_contact_kernel
  next_decisive_test: CENTERED_BOUNDARY_RECOVERY_RELATIVE_GAP
  route_score: 3
```

**Artifact handoff:** only the expected BOUNDARY verdict path is eligible for repository publication. This session made no repository write, commit or push. The accompanying external receipt records the final UTF-8 bytes, SHA-256, locally computed Git blob, LF count and final-LF flag. A later authorized publisher must preserve the actual branch parent and verify that only this new path changes; it must not overwrite either COLLAR version. Publication verifies bytes, not the new paper lemmas.

The independent mathematical gate is to check (BND11)-(BND16) on the literal L18 source, check constant-profile operator-domain membership, and check (BND18)-(BND23) with the full centered domain and signs. Then audit the unpaid comparison separately. There is no Lean file, `lake` command or axiom-profile result from this batch. Standard Lean axioms are not claimed as evidence for a paper theorem.

## 9. PROSHKA'S OWN LINE

I chose averages because their definition does not require a boundary trace limit.  
The new boundary estimate is strong enough to control them but does not determine their sign.  
The singular kernel makes two constant output channels the leading part of the forcing.  
That is a useful source fact, not a proof that only two physical modes matter.  
The first nearby alternative was a shape derivative of the lowest eigenvalue.  
It would require a domain-variation theorem and a treatment of multiple branches.  
The second nearby alternative was direct use of normalized endpoint values.  
Their existence is not a consequence of the bound we actually have.  
I therefore kept the exact finite-width averages and avoided both assumptions.  
The first move beyond this batch is to compare centered recovery with the actual low energies.  
It would fail as a method if every estimate first replaced M by its smallest eigenvalue.  
The second move is the signed two-mean comparison after the centered gate is proved.  
It would fail as a proof if centered strictness were mistaken for strictness of the remaining two-by-two matrix.  
The data I would ask for are exact identities for the centered profiles in (BND29), not more old eigenvalue digits.  
They would have to preserve the prime and pole terms before any inverse is applied.  
The surprising point is that bounded low modes alone control the oscillation of the rescaled response.  
The stronger boundary estimate is needed to reduce the complete mean scale to the right order.  
I distrust the inference from small physical boundary mass to a small inverse-weighted recovery.  
I also distrust a rank-two leading term when the comparison energies have no relative floor.  
The ordinary strip integrals expose that issue without pretending to be normal derivatives.  
A mode can have zero strip integrals without vanishing on either strip.  
The earlier collar injectivity theorem does not remove this distinction.  
The useful result here is an explicit leading matrix and an exact account of the modes it might miss.  
The unresolved result is whether the actual arithmetic source forbids those modes and the final equality.  

## 10. RESEARCH LOG

### 10.1 Sources consulted and what was used

| Source and exact locator | READ / RELAY | Use or limitation |
|---|---|---|
| BOUNDARY request, commit b574857250e2c0e136bb04cfddd906ea1b3aee8f, path and hashes in header | READ full; attached bytes rehashed | Task, canonical COLLAR correction, two new input appendices, exact source, scaled control and response schema. |
| PROSHKA_SYSTEM_PROMPT_v2.md, rh_clean, blob eba04b799176c9e6a1d5f7fc4061280cfbf96ad4 | READ through GitHub, including continuation after initial truncation | Judge protocol, single verdict, source boundaries and no route promotion. |
| [C] CONTACT at SOURCE_BASE; C1-C8, C19-C21 and stated first-contact prerequisites | READ relevant source sections; full bytes rehashed | Literal form, logarithmic domains and full cross operator. The already closed prerequisite campaign was not repeated. |
| [L] canonical COLLAR at SOURCE_BASE, L4-L29, especially L18-L23 and L28-L29 | READ fresh pinned passages, overlapping retrieval after truncation | Actual arithmetic separation, universal collar operator, full source columns, exact high-core feedback and existing unpaid comparison. Fresh full-file SHA remains incomplete. |
| [I] COLLAR_INDEPENDENT_CHECK at SOURCE_BASE, complete file, especially Additional source-boundary derivation and Uniform-boundary extension | READ full; exact staged bytes rehashed | Reconstructed the new L-infinity, common-domain, fixed-graph, scaling and response proofs. Acceptance receipts were not used as analytic axioms. |
| [CI] CONTACT_INDEPENDENT_CHECK at SOURCE_BASE, fresh lines 1-32 | READ scope/provenance; mathematical acceptance is report evidence | Confirms the intended partial scope and preservation of C22 as unpaid. No fresh full-file SHA or repeat of its whole audit is claimed. |
| [BP] docs/BATCH_PATTERNS.md at SOURCE_BASE | READ full; exact staged bytes rehashed | Proof-construction, concrete repair, own-line and research-log requirements. This is the explicitly requested file outside routeB_bus. |
| [H] arXiv:2401.18033v2, exact HTML URL in section 0.2; Theorem 1.1, (1.2), (1.14)-(1.19), section 4 proof, Lemma A.3 and proof | READ primary rendered HTML | Version, hypotheses, boundary decay and weak scaling. Raw HTML bytes not matched to parent's hash. Hopf conclusion not imported; external dependency proofs not all repeated. |
| Older uncommitted local COLLAR named in request | EXCLUDED, not substituted | Its different hash and L-label inventory are not the canonical source for this batch. |
| GitHub create/write-tool discovery and Plugin_Management search | READ capability results | No usable write action returned; the installed integration listing was not treated as a successful commit. |
| Read-only Git connectivity check and failed raw-file acquisition attempts | EXECUTED / UNAVAILABLE | DNS failure prevents CLI publication and raw-byte acquisition. These failures provide no mathematical evidence. |
| Expected BOUNDARY verdict path on rh_clean | READ attempted; Not Found | No historical verdict was overwritten. This does not itself publish the local file. |

### 10.2 Branches attempted or withheld

| Branch | First failed assertion or exact reason not promoted |
|---|---|
| Absolute O(d) recovery plus o(d) feedback gives strictness | Packet control has exact S=0; no signed comparison with M is supplied. |
| Order-d gap from the new rank-two leading matrix | (BND17) is not derived; (BND16) records cancellation along any hypothetical source null direction. |
| Replace all collar profiles by a scalar inverse | Canonical L14 refutes relative operator-norm convergence. Only the restricted two-profile graph estimate (BND13) is used here. |
| Discard centered profiles because their recovery is o(d) | (BND26) has centered recovery exactly equal to M and a negative half-energy success margin. |
| Use two strip means as an automatically injective boundary measurement | The exact missing statement is (BND24); dimension and sign-changing branches are not discharged. |
| Apply CONTACT collar injectivity to zero strip integrals | Zero integrals are not zero functions on the two strips; the premises do not match. |
| Derive Hadamard coefficients from the boundary bound | No normalized trace limit or differentiable cluster transport was proved. The finite-width repair avoids these premises. |
| Use positive full-source semigroup or drop the odd reflected prime | Neither is justified; the absolute perturbation domination is different, and (BND10)/(BND29) retain the atom. |
| Declare exact mean/centered elimination a complete lower-sign proof | (BND25) leaves two genuine source signs. No generic Schur identity supplies them. |

### 10.3 Reusable intermediate identities and their limits

(BND10) is a literal signed source expression for the averaged forcing, valid without trace limits.  
(BND11) bounds its centered oscillation on the complete low space with no rank factor.  
(BND12) distinguishes the constant-channel value 1 from the universal lower floor log2.  
(BND13) gives restricted scalarization on two graph-controlled profiles while respecting the whole-operator obstruction.  
(BND14)-(BND16) identify a rank-at-most-two leading source response and its conditional cancellation at contact.  
(BND19) is an exact inverse decomposition, with every infinite centered and high-core contribution retained.  
(BND23) identifies the first repaired kernel with vanishing ordinary integrals on both physical strips.  
(BND25) separates centered strictness from the remaining two-mean sign.  
(BND26) shows why even subleading centered recovery cannot be discarded relative to unknown low energies.  
(BND29) is the exact new centered source functional for the single next test.  

The exact symbolic checks verify finite algebra only. No numerical source energy, approximate eigenspace, source discretization, interval certificate, or Lean proof was run. The complete delivery receipt is external to these hashed verdict bytes. The present artifact remains NOT_COMMITTED / NOT_PUSHED.
