# STATUS: TRY_CONTACT_COUPLED_COLLAR_CONTRACTION
```yaml
OPERATIVE_CLASS: TRY_CONTACT_COUPLED_COLLAR_CONTRACTION
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-10-CONTACT
BOUNDARY_ID: GOAL058_FIRST_CONTACT_SOURCE_KERNEL_EXTERIOR_RIGIDITY
RESULT:
  Q1: PROOF_CANDIDATE_COMPLETE
  Q2: PARTIAL_WITH_PRECISE_REMAINDER
  Q3: PARTIAL_WITH_PRECISE_REMAINDER
  OVERALL: PARTIAL_WITH_PRECISE_REMAINDER
VERIFIER: PAPER
FIRST_CONTACT_PREREQUISITES_PROVED: true
SOURCE_KERNEL_EXCLUSION_PROVED: false
LOWER_SIGN_PROVED: false
INDEPENDENT_CHECK_OF_NEW_LEMMAS: PENDING
LEAN_VERIFIED: false
PX_RH_CLAIM: NOT_MADE
REQUEST_LOCK:
  COMMIT: 4bf7ce2a65c380c6107ba204c75697029fdb8c2f
  BLOB: 3843a5479cc6b8c905bd6663d680f195133a2e46
  SHA256: d2abcb9164c5a84ab6fe383dbb7a9aab38d8cf2958465182b9b6af120260f9db
  BYTES: 14481
  LINES: 88
  FINAL_LF: true
  LOCAL_ATTACHMENT_HASHES_RECOMPUTED: true
  EXACT_COMMIT_CONNECTOR_BLOB_MATCH: true
SOURCE_BASE: e915833ca99320dd03899fbfe296502ff0120db2
BOOTSTRAP_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
SHELF_VERIFICATION:
  PINNED_BLOBS_MATCHED: 8
  FULL_SHA256_RECOMPUTED_MATCH: 3
  COMPLETE: false
  SHA256_RECOMPUTED_KEYS: [E, S, B]
  SHA256_NOT_RECOMPUTED_KEYS: [H, D, I, X, J]
  LIMITATION: section_0
FIRST_INCORRECT_ASSERTION:
  E1_E5: NONE_FOUND
  D14_D20_D21_D36_H16_H17_AT_STATED_SCOPE: NONE_FOUND
  ATTEMPTED_SHORTCUT: local_nonnegativity_does_not_control_exterior_coupling
FIRST_FAILURE:
  Q1: NONE_REMAINING_IN_THIS_PAPER_DERIVATION
  Q2_INITIAL: E4_does_not_imply_vanishing_on_an_exterior_collar
  Q2_REPAIR: strict_contraction_of_the_full_source_collar_transfer_is_unproved
  Q3: source_strict_contraction_required_before_all_test_sign
PROVED_SOURCE_LEMMAS:
  - fixed_window_closed_form_compact_resolvent_and_continuous_bottom
  - explicit_small_window_anchor_a0_equals_exp_minus_20_over_2
  - endpoint_inclusive_Carleman_bound_for_exterior_defect
  - no_endpoint_supported_distribution_in_the_local_E_dual
  - two_sided_collar_response_injective_on_each_window_kernel
  - any_nonzero_null_mode_gives_negative_energy_in_every_larger_window
  - sharp_core_collar_split_with_bounded_full_source_cross_operator
  - collar_floor_tends_to_positive_infinity_as_collar_width_tends_to_zero
  - compact_coupled_transfer_exactly_classifies_the_window_sign
MINIMAL_MISSING_ESTIMATE: strict_full_source_collar_contraction_C22
PREDICTION_FATES:
  P1: {probability: 0.90, fate: CONFIRMED}
  P2: {probability: 0.95, fate: CONFIRMED}
  P3: {probability: 0.80, fate: CONFIRMED}
PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SECOND_EXPRESSION
SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
EXECUTION:
  NEW_NUMERICAL_RUN: false
  OLD_FINITE_ROWS_RERUN: false
  SATURATION_A22_RERUN: false
  E5_CHECK: exact_algebra_only
  LEAN_EDIT: false
  LEAN_GATE: NOT_RUN
  CONTROL_QUEUE_REGISTRY_EDIT: false
PUBLICATION:
  AUTHORIZED_WRITE_SCOPE: VERDICT_DOC_ONLY
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CONTACT_2026-09-10.md
  BRANCH: rh_clean
  COMMIT_STATUS: COMMITTED_VIA_GITHUB_CONTENTS_API
  PUSH_STATUS: REMOTE_BRANCH_UPDATED_DIRECTLY
  COMMIT_BLOB_SHA256_BYTES_LINES: accompanying_delivery_receipt
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
```

## 0. Decision and source integrity

**The first-contact spectral prerequisites can be proved for the literal form. The source kernel exclusion is not proved.** The new result is not another assertion that radical tails are orthogonal. A nonzero local null mode has a nonzero response in *every two-sided exterior collar*. It therefore gives a strictly negative trial in every larger window. This proves immediate crossing, not impossibility of first contact. [ABSTRACT][PAPER]

A concrete repair localizes the unresolved sign to two *interior* boundary strips. Their own full-source form has an independently proved lower bound tending to infinity as their width decreases. Their coupling to the positive smaller window is an explicit bounded operator, including a Carleman singular integral, every applicable prime shift and both poles. The remaining estimate is strict contraction of this coupled operator after the two actual positive form inverses. The available estimates do not prove strictness. [ABSTRACT][PAPER for the reduction][CONDITIONAL for strictness]

The request attachment was read in full and rehashed: its 14,481 bytes, 88 LF characters, SHA-256 and Git blob match the delivery. The connector fetched that path at the exact request commit. The bootstrap was freshly fetched on `rh_clean`; the final part was also read, not inferred from the older uploaded bootstrap.

**Incomplete check, explicitly retained:** all eight shelf paths were fetched at SOURCE_BASE and their returned blobs matched. Full independent SHA-256 recomputation was completed for E, S and B only. It was **not** completed for H, D, I, X or J. Those five SHA-256 entries below are declared source locks, not a claim of a fresh hash calculation. A failed raw-HTTP acquisition was not counted as verification. The substantive lemmas used for CONTACT are rederived below; historical acceptance is not substituted for a proof.

| Key | Path relative to repository root | SHA-256 at SOURCE_BASE | Git blob | Reading and hash status |
|---|---|---|---|---|
| E | `docs/routeB_bus/FIRST_CONTACT_EXTERIOR_2026-09-10.md` | `b5869eb1573d7d25ce0c11ce08184643e71e6323cdbed6e4195e95c3b0de8560` | `34a54f8154efc3c072ac030485cb3320d231f507` | READ full; both hashes recomputed, match; 9448 bytes, 93 lines |
| H | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SCREW_HYPERBOLICITY_HODGE_2026-09-08.md` | `dc406f3b5e8a6074df50c542b707bfb941bc4c8daf50433a3a71641e4064cc89` | `654f73ab347539511e507861f8eba79ad4ffc0f4` | READ source distinctions and section 6, especially H15-H17; blob matched; SHA not recomputed |
| D | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_DISTANCE_2026-09-09.md` | `2ad89fd43395242af8de2ed61383dd481057ae079cbd109aa32443e25edf1c5c` | `11979ce43d5e974080afa6690bb81e07f67f745e` | READ source/domain arguments and D14, D20-D21, D36; blob matched; SHA not recomputed |
| S | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SATURATION_2026-09-10.md` | `268093822b4ab75c6b7f8efd725172db9b2de96ad5c61924da3eb3f9dd0a50a5` | `0893efc7cd4427e568fd6fe4b97eaaad92b81435` | Local complete artifact rehashed; pinned blob matched; READ relevant scope/domain statements; A22 not rerun |
| I | `docs/routeB_bus/SATURATION_INDEPENDENT_CHECK_2026-09-10.md` | `d555fd6a2fd480369670f81fe3f1debd07255ced61807fa2c0aae4f7a8ea2796` | `b687cf1939572f45c35dccb73e9fe5474e60d9f2` | READ report, source limitations and final transfer; acceptance is RELAY evidence; SHA not recomputed |
| X | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_WEIL_POSITIVITY_AROUND_XI_PROOF_2026-09-05.md` | `93db2de6357821918211a8033b2c8f34e7f684320a25e5623e1f24d33ed58fe9` | `136aceb3cbbabcdfa425459562b803b67c548b48` | READ source/domain and signed-transform scope; no new GS/DOM proof claimed; SHA not recomputed |
| J | `docs/routeB_bus/AGENT_REPORT_2026-09-05_GOAL058_XIDEV_INDEPENDENT_AUDIT.md` | `b2914990a93020bf3f2dbbcd3e3a8a9cb836c2ce294a85933290db048d21848f` | `938d9b11e659adb905e70df1ae175e5a35aeb701` | READ sections 0-2; historical computations remain RELAY, not reruns; SHA not recomputed |
| B | `docs/BATCH_PATTERNS.md` | `cded6dfd5950fd8dd230ad770ff0cf4a50a5bea9b2d5e91601b8eaa76120903b` | `cb63bab5fbff3d39bf63c0b0f081a2264e004f2b` | READ full; both hashes recomputed, match; 11341 bytes, 79 lines |

`docs/BATCH_PATTERNS.md` is the only task-required read outside `docs/routeB_bus/`. No file there was modified. The three fresh shelf hashes identify bytes, not mathematical validation. No PDF was read or numerically certified in this batch.

The freshly read primary Suzuki HTML is labelled `arXiv:2606.09096v1`, with a June 8 header but an **August 24, 2026 body date**. It is not identified with the shelf's local June v1 PDF, nor with v2. Its introduction independently checks the literal Weil functional and all-complex compact-smooth consumer. The proofs below do not import its continuity or nondegeneracy conclusions as premises. [ABSTRACT][PAPER, provenance audit]

## 1. Q1 — the actual form domain and first-contact consumer

All lemmas in sections 1-2 are [ABSTRACT][PAPER]. Their quantifiers range over arbitrary fixed real windows and arbitrary complex functions, not only even functions.

### 1.1 Literal form, continuity, and translations

Use \(U_t f(x)=f(x-t)\), the antilinear-first inner product, and
\[
\alpha(t)=\frac{e^{-t/2}}{1-e^{-2t}},\quad
c_A=\gamma+\log(8\pi)+\pi/2,\quad w_n=\Lambda(n)/\sqrt n.
\]
Define \(\mathcal D\), \(\mathcal W\), \(M_\pm\) and \(B\) exactly as in the request, with
\[
\begin{split}
B(f,g)={}&\int_0^\infty\alpha(t)\langle U_tf-f,U_tg-g\rangle_2dt
-c_A\langle f,g\rangle_2\\
&-\sum_{n\ge2}w_n\{\langle f,U_{\log n}g\rangle_2+
\langle f,U_{-\log n}g\rangle_2\}\\
&+\overline{M_+(f)}M_-(g)+\overline{M_-(f)}M_+(g).
\end{split} \tag{C1}
\]
The change from forward to backward differences leaves the form unchanged. Weighted Cauchy-Schwarz gives
\[
|\langle f,U_tg\rangle_2|\le e^{-|t|}\sqrt{\mathcal W[f]\mathcal W[g]},
\qquad |M_\pm(f)|\le\sqrt{4/3}\sqrt{\mathcal W[f]}.
\]
The elementary first-term-plus-integral estimate gives \(\sum_{n\ge2}\log n/n^{3/2}<6\), and \(c_A<7\). Consequently
\[
|B(f,g)|\le22\|f\|_E\|g\|_E,
\qquad \|f\|_E^2=\mathcal W[f]+\mathcal D[f]. \tag{C2}
\]
Completeness follows from the closed graph of the translated-difference map into its product \(L^2\) space.

**Translation covariance is exact**, including the poles:
\[
B(U_t f,U_t g)=B(f,g),\qquad
M_\pm(U_t f)=e^{\pm t/2}M_\pm(f),\qquad
\|U_t f\|_E\le e^{|t|}\|f\|_E. \tag{C3}
\]
The reciprocal pole factors cancel in each polarized term. This is a property of the fixed source, not a deformation of its arithmetic parameters.

### 1.2 Logarithmic form domain and compact embedding

Take the unitary angular-frequency transform \(\widehat f(\xi)=(2\pi)^{-1/2}\int e^{-i\xi x}f(x)dx\). This auxiliary Fourier coordinate does not change the fixed source form. Tonelli and Plancherel give
\[
\mathcal D[f]=\int_{\mathbb R}m(\xi)|\widehat f(\xi)|^2d\xi,
\quad
m(\xi)=2\sum_{j\ge0}\frac{\xi^2}{\beta_j(\beta_j^2+\xi^2)},
\quad \beta_j=2j+\tfrac12. \tag{C4}
\]
Indeed \(\alpha(t)=\sum_j e^{-\beta_jt}\) and
\(\int_0^\infty e^{-\beta t}(1-\cos\xi t)dt=\xi^2/[\beta(\beta^2+\xi^2)]\).
Splitting the sum at \(\beta_j\simeq|\xi|\) proves
\(1+m(\xi)\asymp1+\log(2+|\xi|)\); in particular \(m(\xi)\to\infty\).
The constants in this comparison are fixed numerical constants, not positivity assumptions about Q.

On functions supported in \([-a,a]\), \(\mathcal W\) lies between \(\|f\|_2^2\) and \(e^{2a}\|f\|_2^2\). Thus the E norm is equivalent there to \(\|f\|_2^2+\mathcal D[f]\). In fact
\[
V_a=\{f\in E:\ f=0\text{ a.e. outside }[-a,a]\}. \tag{C5}
\]
Here is a proof without imposing a trace. For such an f, inward dilations
\(f_r(x)=r^{-1/2}f(x/r)\), \(r\uparrow1\), converge in the logarithmic Fourier norm. To see this, dilation is uniformly bounded for \(1/2\le r\le1\) by the weight comparison in C4, and converges on smooth Fourier profiles of compact support, which are dense in weighted Fourier \(L^2\). Approximation then proves convergence for every f. The supports stay in a fixed bounded interval, so weighted physical convergence follows as well. Each \(f_r\) has a positive support margin inside \((-a,a)\); mollify at a smaller radius. Fourier dominated convergence proves convergence in \(\mathcal D\), while the support margin is preserved. This proves C5 and the asserted core.

For completeness, a sharply cut \(C^1\) profile has \(\|U_tf-f\|_2^2\le C t+C't^2\) near zero, including both endpoint jumps. Its energy is finite. Inward tapers have error squared \(O(\varepsilon(1+|\log\varepsilon|))\). Thus the familiar discontinuous cuts really are in this domain. Nothing identifies \(V_a\) with \(H^1_0(-a,a)\).

Bounded subsets of \(V_a\) are relatively compact in \(L^2(-a,a)\). C4 bounds the Fourier mass beyond R by a quantity tending uniformly to zero. Restricting the Fourier cutoff \(|\xi|\le R\) back to \((-a,a)\) is a Hilbert-Schmidt operator: its kernel on the bounded square is the usual bounded sine kernel. Compact Fourier cutoffs therefore approximate the inclusion in operator norm. This proves compact embedding directly.

### 1.3 Closed semibounded form and bottom attainment

Set
\[
s_a=\sum_{2\le n\le e^{2a}}w_n,
\qquad L_a=c_A+2s_a+4\sinh a.
\]
Window overlaps vanish for \(\log n\ge2a\), with equality harmless a.e. The prime term is bounded in absolute value by \(2s_a\|f\|_2^2\), and the pole term by \(4\sinh a\|f\|_2^2\). Therefore
\[
Q[f]\ge\mathcal D[f]-L_a\|f\|_2^2. \tag{C6}
\]
The remaining terms are an \(L^2\)-bounded Hermitian perturbation of \(\mathcal D\). The shifted form \(Q+(L_a+1)\|\cdot\|_2^2\) has a norm equivalent to the complete norm from C4-C5, hence is closed.

Define its **Friedrichs operator** by
\[
\begin{split}
D(A_a)=\{v\in V_a:\ &\exists g\in L^2(-a,a),\ 
 B(h,v)=\langle h,g\rangle_2\ \forall h\in V_a\},\\
&A_av=g. \tag{C7}
\end{split}
\]
The shifted coercive form solves each resolvent equation by the Hilbert-space representation theorem. Its inverse is self-adjoint and compact by the compact embedding just proved. Thus \(A_a\) is self-adjoint, bounded below, and has compact resolvent; every eigenspace has finite dimension.

Alternatively, bottom attainment follows directly. A unit minimizing sequence has bounded \(\mathcal D\) by C6. Extract a weak form-norm and strong \(L^2\) limit. The limit still has norm one; \(\mathcal D\) is lower semicontinuous and all perturbation terms are \(L^2\)-continuous. It attains the minimum. Complex variations give
\(B(h,v)=\lambda_a\langle h,v\rangle_2\) for all h. This proves the actual D14 assertion, including attainment and its domain.

### 1.4 D20-D21 lineage and continuity in the window

Expanding C1 against a compact smooth test gives, on \((-a,a)\),
\[
A_av=\int_0^\infty\alpha(t)(2v-U_tv-U_{-t}v)dt-c_Av
-\sum_{n\le e^{2a}}w_n(U_{\log n}v+U_{-\log n}v)
+e^{x/2}M_-(v)+e^{-x/2}M_+(v). \tag{C8}
\]
This is D20, interpreted as a distribution/form equation, not a pointwise integral for every form-domain vector.

Let \(K\) denote the convolution distribution in C8. If \(-g''=K\), the double integration by parts on the compact smooth core gives
\[
B(h,v)=\iint g(x-y)\overline{h'(x)}v'(y)dxdy. \tag{C9}
\]
This checks D21's two derivative factors and its sign. An affine ambiguity of the primitive disappears because both derivative integrals are zero. The screw primitive is continuous: the local \(1/|t|\) finite-part singularity of K has a continuous double primitive, its atoms have continuous piecewise-linear double primitives, and its other terms are locally integrable. C9 determines the same Friedrichs form closure; it does not assert that every element of \(V_a\) has an \(L^2\) derivative, or that \(Q[v]=\langle v,G_av\rangle\).

For continuity, transport to \((-1,1)\) by \(U^{\rm dil}_a u(x)=a^{-1/2}u(x/a)\). The common form domain is \(V_1\), by C4-C5. Its energy kernel is \(a\alpha(at)\). For a,b in a fixed compact subset of \((0,\infty)\),
\[
\int_0^\infty|a\alpha(at)-b\alpha(bt)|dt\le C|\log(a/b)|. \tag{C10}
\]
Indeed \(\alpha(t)=1/(2t)+1/4+O(t)\) at zero and
\(\alpha(t)+t\alpha'(t)\) is integrable on \((0,\infty)\); differentiate in the dilation parameter and integrate. Thus the difference of the two Dirichlet energies is bounded by \(4C|\log(a/b)|\|u\|_2^2\).

The remaining prime terms can be written with one fixed finite set \(n\le e^{2a_{\max}}\), and shifts \(\log n/a\). Each shift is strongly continuous in \(L^2\). Terms whose shifts exceed 2 vanish; at the threshold their overlap is also zero. Pole terms are finite-rank forms with kernels depending continuously on a. No discontinuous prime-cutoff approximation is made.

A fixed trial gives upper semicontinuity of \(\lambda_a\). For lower semicontinuity, dilated unit minimizers along \(a_j\to a\) have uniformly bounded \(\mathcal D\), using C6 and C10. Compactness gives a strongly \(L^2\)-convergent subsequence. Strong continuity of the finitely many shifts, continuity of the pole forms and lower semicontinuity of the common Dirichlet energy give \(\lambda_a\le\liminf_j\lambda_{a_j}\). Hence \(a\mapsto\lambda_a\) is continuous. This proof does not assume operator-norm continuity of translations on all of \(L^2\).

Nested supports give \(\lambda_b\le\lambda_a\) for b>a. Reflection commutes with the full form, so both parity sectors are retained; the proof never selects an even ground state or assumes simplicity.

### 1.5 An explicit anchor and the conditional consumer

For \(2a<\log2\), D36 follows from disjoint translates for \(t\ge2a\):
\[
Q[v]\ge\left(2\int_{2a}^\infty\alpha(t)dt-c_A-4\sinh a\right)\|v\|_2^2.
\]
Take
\[
\boxed{a_0=\tfrac12e^{-20}.}\tag{C11}
\]
For \(0<t\le1\), \(\alpha(t)\ge e^{-1/2}/(2t)>1/(4t)\). Thus
\(2\int_{2a_0}^{1}\alpha(t)dt>10\).
Also \(c_A<7\), \(4\sinh a_0<1\), and \(2a_0<\log2\), all by elementary exponential bounds. Therefore \(\lambda_{a_0}>2\). No decimal eigenvalue certificate is used.

If any later window is nonpositive, continuity and the anchor give
\[
a_*:=\inf\{a\ge a_0:\lambda_a\le0\}>a_0,
\quad\lambda_{a_*}=0,
\quad\lambda_b>0\ (a_0\le b<a_*).
\]
C7 supplies a nonzero kernel vector. Consequently the requested H17 first-contact exclusion would imply \(\lambda_a>0\) on every finite window, and hence \(Q[f]\ge0\) for every complex compact smooth f. This implication is proved; its exclusion premise is not. [COFINAL_FAMILY][CONDITIONAL]

**Q1 closeout:** no unpaid analytic prerequisite remains in the submitted paper argument. The theorem is not a Lean result or an independently audited proof yet.

## 2. Q2, first attempt — exact exterior analysis and its limit

### 2.1 Audit of E1-E4, on both sides

Expanding C1 on separated supports gives precisely E1-E2, with coefficient \(-1\), not \(-2\), on the off-diagonal integral. For x>a,
\[
R_a^+[v](x)=e^{x/2}M_-(v)-\sum_{j\ge1}e^{-\beta_jx}M_j^+(v)
-\sum_{n\ge2}w_nv(x-\log n),
\quad M_j^+(v)=\int e^{\beta_j y}v(y)dy. \tag{C12}
\]
For x<-a the equally necessary equation is
\[
R_a^-[v](x)=e^{-x/2}M_+(v)-\sum_{j\ge1}e^{\beta_jx}M_j^-(v)
-\sum_{n\ge2}w_nv(x+\log n),
\quad M_j^-(v)=\int e^{-\beta_j y}v(y)dy. \tag{C13}
\]
In each formula the j=0 term cancels exactly one pole. On a compact exterior set the prime sum is finite and the geometric series and its derivatives converge uniformly. Only the geometric part is asserted analytic. No representative values or traces of v are used.

For every global radical r whose cut belongs to \(V_a\), local nullity implies
\(B(r_{\rm out},v)=B(r,v)-B(r_{\rm in},v)=0\).
Thus E4 is correct but adds no new equation. Its Bessel specialization uses only the stated cut/radical hypotheses, not the cofinal T-squared estimate.

**FIRST_FAILURE of the continuation attempt:** the implication
\[
\{B(r_{\rm out},v)=0\text{ for the known radicals}\}
\Longrightarrow R_a^+[v]=R_a^-[v]=0
\]
has no proved exterior-density premise. Interior density cannot fill that premise. E5 below refutes the corresponding structure-only argument.

### 2.2 New source lemma: the defect is L2 up to the boundary

Put \(k(t)=\alpha(t)-1/(2t)\), continuously extended at zero. On any bounded positive interval, k is bounded. For x=a+s, \(0<s<d\), the exact *unexpanded* exterior expression is
\[
\begin{split}
R_a[v](a+s)={}&-\frac12\int_0^{2a}\frac{v(a-t)}{s+t}dt
-\int_0^{2a}k(s+t)v(a-t)dt\\
&+e^{(a+s)/2}M_-(v)+e^{-(a+s)/2}M_+(v)
-\sum_{n\le e^{2a+d}}w_nv(a+s-\log n). \tag{C14}
\end{split}
\]
The reflected formula uses \(v(-a+t)\) and \(v(-a-s+\log n)\). Keeping the unexpanded poles here does not undo C12-C13's exact cancellation.

The **Carleman operator** \(f\mapsto\int_0^\infty f(t)/(s+t)dt\) has \(L^2\) norm at most \(\pi\). Proof: under the unitary substitution \(t=e^u\), \(f(e^u)e^{u/2}\), it becomes convolution with \(1/[2\cosh(u/2)]\), whose integral is \(\pi\). Young's inequality proves the bound, also for interval restrictions.

C14's first term is therefore bounded in \(L^2(0,d)\) by \((\pi/2)\|v\|_2\). The regular integral is Hilbert-Schmidt, the two pole terms have finite rank, and the finitely many shifts are bounded in \(L^2\). Consequently
\[
 v\longmapsto R_a[v]|_{(-a-d,-a)\cup(a,a+d)}
 \quad\text{is bounded }L^2(-a,a)\to L^2\text{ of the collar}. \tag{C15}
\]
This includes approach to both endpoints, a strengthening of merely local exterior regularity. It does not assert analytic continuation of the prime-shift term.

### 2.3 Endpoint-supported defects cannot be hidden

Let a distribution supported on finitely many points be continuous for the local E norm. It is zero. Indeed such a distribution is a finite sum of derivatives of Dirac masses. A test
\(h_\varepsilon(x)=\varepsilon^j\psi((x-x_0)/\varepsilon)\), with its prescribed j-th jet at \(x_0\) and the other relevant jets zero, isolates each coefficient. Directly splitting the translation integral at \(\varepsilon\) and 1 gives
\[
\|h_\varepsilon\|_E^2
\le C\varepsilon^{2j+1}(1+|\log\varepsilon|)\longrightarrow0. \tag{C16}
\]
Below \(\varepsilon\), use \(t^2\|h_\varepsilon'\|_2^2\); above it use \(4\|h_\varepsilon\|_2^2\). Weighted mass is bounded on the common compact support. Continuity forces every isolated coefficient to vanish. This explicitly pays the possible two endpoint distributions; no trace of v is assumed.

### 2.4 New rigidity lemma: no invisible two-sided collar

For every a,d>0,
\[
 v\in\ker A_a,
 \quad R_a[v]=0\text{ on }(-a-d,-a)\cup(a,a+d)
 \quad\Longrightarrow\quad v=0. \tag{C17}
\]
**Proof.** The global distribution \(h\mapsto B(h,v)\) vanishes in \((-a,a)\) and both collars. Any defect at \(\pm a\) vanishes by C2 and C16. Thus it vanishes throughout \((-a-d,a+d)\).
Set c=a+d/2. For every \(|t|<d/4\), the translate \(U_tv\) is supported strictly inside \((-c,c)\) and belongs to \(V_c\). By C3 its distributional equation vanishes on \((-c,c)\); C2 and the form core extend this to all tests in \(V_c\). Thus \(U_tv\in\ker A_c\).
If v is nonzero, arbitrarily many distinct translates are linearly independent. To verify this, Fourier transform a finite relation. The continuous transform of the nonzero compactly supported L2 function v is nonzero on some open real interval. On that interval the exponential polynomial \(\sum_j c_j e^{-it_j\xi}\) vanishes; analytic uniqueness and a Vandermonde matrix give every \(c_j=0\). This contradicts the finite-dimensional kernel furnished by compact resolvent. Therefore v=0. □

In particular a compactly supported global radical must vanish. This last implication needs no zero-count theorem and no assumption about multiplicities of zeta zeros. But C17 is **not** local-to-exterior continuation: it proves uniqueness *after* both exterior defects are zero, not why they should be zero.

### 2.5 What the defect actually produces: immediate negative crossing

Let \(H_{a,d}^{\rm out}\) be the E-closure of smooth tests in the two exterior collars, and let \(r_v\in E\) represent \(B(\cdot,v)\). Put \(h_{a,d}=P_{H_{a,d}^{\rm out}}r_v\). Then
\[
B(h_{a,d},v)=\|h_{a,d}\|_E^2.
\]
For nonzero \(v\in\ker A_a\), C17 implies \(h_{a,d}\ne0\). Normalize \(\|v\|_2=1\). Disjoint physical supports and C2 give the actual source trial
\[
Q[v-h_{a,d}/22]\le-\|h_{a,d}\|_E^2/22,
\quad
\lambda_{a+d}\le
-\frac{22\|h_{a,d}\|_E^2}{484+\|h_{a,d}\|_E^2}<0. \tag{C18}
\]
The Riesz vector is used to expose a negative *coupled* form, not to manufacture a positive square representing Q.

On the finite-dimensional unit sphere of \(\ker A_a\), injectivity gives a positive lower bound for \(\|h_{a,d}\|_E\), for each fixed d. It is not uniform as d tends to zero. In fact \(h_{a,d}\to0\) in E: these orthogonal projections are onto decreasing closed subspaces with intersection zero. The standard projection identity makes the projected vectors Cauchy, and their limit belongs to every subspace, hence is zero. Convergence is uniform on this finite-dimensional sphere.

**Interpretation:** a putative first contact must cross immediately into negative windows. That is compatible with the definition of first contact. Inferring a contradiction here would silently assume nonnegativity of a larger window. Neither E4 nor the upper T-squared supplier supplies that assumption.

## 3. Q2, concrete repair — eliminate the positive core, not the source terms

All proved assertions in this section are [ABSTRACT][PAPER]; C22 is the explicitly [COFINAL_FAMILY][CONDITIONAL] missing assertion.

### 3.1 Exact splitting, with the internal cut boundaries paid

Fix 0<b<a, put d=a-b, and split the physical interval into
\(I_b=(-b,b)\) and \(J_{a,b}=(-a,-b)\cup(b,a)\).
Let \(Y_{a,b}=\{w\in V_a:w=0\text{ a.e. on }I_b\}\).
Sharp restriction gives a bounded decomposition
\[
V_a=V_b\dotplus Y_{a,b},
\qquad u=\mathbf1_{I_b}v,\quad w=\mathbf1_{J_{a,b}}v.
\]
Here is a source proof of bounded cutting. Set
\(k_a^{\rm reg}=\sup_{0<t\le2a}|\alpha(t)-1/(2t)|<\infty\).
Between the core and either adjoining collar, the singular kernel is a restricted half-Carleman operator. The two sides together have norm at most \(\pi\); the regular kernel has norm at most \(2a k_a^{\rm reg}\).
For the energy truncated at translation length \(\varepsilon\), its cross pairing is exactly minus this truncated off-diagonal integral. Its absolute value is uniformly bounded by
\((\pi+2a k_a^{\rm reg})\|u\|_2\|w\|_2\), by applying the positive kernel bound to absolute values. Thus
\[
\mathcal D_\varepsilon[u]+\mathcal D_\varepsilon[w]
\le\mathcal D[v]+(\pi+2a k_a^{\rm reg})\|v\|_2^2.
\]
Monotone convergence proves finite energies and bounded projections. C5 gives domain membership. The weight splits exactly. This covers all four boundaries \(-a,-b,b,a\), not just the original two endpoints.

The cross operator \(J_{a,b}^{\rm src}:L^2(J_{a,b})\to L^2(I_b)\) is explicitly
\[
\begin{split}
(J_{a,b}^{\rm src}w)(x)={}&-\int_{J_{a,b}}\alpha(|x-y|)w(y)dy
-\sum_{n\le e^{2a}}w_n\{w(x-\log n)+w(x+\log n)\}\\
&+e^{x/2}M_-(w)+e^{-x/2}M_+(w),\qquad x\in I_b. \tag{C19}
\end{split}
\]
It represents \(B(u,w)=\langle u,J_{a,b}^{\rm src}w\rangle_2\); the mass cross term is zero by disjoint support. A safe explicit bound, independent of b, is
\[
\|J_{a,b}^{\rm src}\|\le M_a,
\qquad M_a=\pi+2a k_a^{\rm reg}+2s_a+4\sinh a.
\]
The prime shifts have norm at most one each; the pole operator bound is the full-window bound. No prime-only recovery is substituted.

### 3.2 The thin collars themselves are strongly positive

Let \(C_{a,b}\) be the Friedrichs operator of Q on \(Y_{a,b}\), in physical collar L2. It is closed, semibounded and has compact resolvent by section 1.
Each individual interval of length d has Dirichlet energy at least
\(2\int_d^\infty\alpha(t)dt\) times its squared norm. The cross energy between the two collars is bounded below by
\(-d\alpha(2b)\|w\|_2^2\): their separation is at least 2b, \(\alpha\) is decreasing, and each L1 norm is at most \(\sqrt d\) times the corresponding L2 norm. Retaining the complete prime and pole bounds yields
\[
C_{a,b}\ge\eta(a,b)I,\qquad
\eta(a,b)=2\int_d^\infty\alpha(t)dt-c_A-2s_a-4\sinh a-d\alpha(2b).
\tag{C20}
\]
For every fixed a>0, \(\eta(a,b)\to+\infty\) as b increases to a. In fact it is \(\log(1/d)+O_a(1)\), by \(\alpha(t)=1/(2t)+O(1)\). This is an unconditional full-source collar floor, not a claim of positivity on the whole window.

### 3.3 Exact normalized coupling and the missing strict inequality

Suppose \(\lambda_b>0\) and choose b sufficiently close to a that \(\eta(a,b)>0\). Both inverses below are now licensed by independent, explicit hypotheses:
\[
\mathcal K_{a,b}=A_b^{-1/2}J_{a,b}^{\rm src}C_{a,b}^{-1/2}.
\]
This is a compact operator between the two physical L2 spaces. Compactness follows from compact resolvent of the positive operators; the cross operator is bounded. Completing the form square, for \(v=u+w\), gives
\[
\begin{split}
Q[v]={}&Q_b[u+A_b^{-1}J_{a,b}^{\rm src}w]
+Q[w]-\langle J_{a,b}^{\rm src}w,A_b^{-1}J_{a,b}^{\rm src}w\rangle_2\\
={}&Q_b[u+A_b^{-1}J_{a,b}^{\rm src}w]
+\|y\|_2^2-\|\mathcal K_{a,b}y\|_2^2,
\qquad y=C_{a,b}^{1/2}w. \tag{C21}
\end{split}
\]
This keeps the actual inverse *inside* the coupled source expression. Its expansion includes all archimedean/prime/pole mixed terms.

Consequently the following is an exact sign classifier, not merely a sufficient majorant:
\[
\lambda_a>0\iff\|\mathcal K_{a,b}\|<1,\qquad
\lambda_a=0\iff\|\mathcal K_{a,b}\|=1,\qquad
\lambda_a<0\iff\|\mathcal K_{a,b}\|>1.
\]
For norm less than one, C21 and the bounds on the two positive diagonal forms give a positive floor. Explicitly, with \(\Delta=1-\|\mathcal K_{a,b}\|^2>0\), one floor is
\[
\min\left\{\lambda_b/2,
\frac{\Delta\eta(a,b)}{1+2(M_a/\lambda_b)^2}\right\}.
\]
For norm equal to one, compactness attains that norm; choose a maximizing y, put \(w=C_{a,b}^{-1/2}y\), and \(u=-A_b^{-1}J_{a,b}^{\rm src}w\). C21 gives a nonzero null vector of the nonnegative full form. For norm greater than one the same construction gives negative energy. This proves every direction and does not assume simplicity.

The precise remaining source assertion for this mechanism is
\[
\boxed{\begin{gathered}
\forall a>a_0:\quad
\bigl[\lambda_a=0\ \land\ \forall c\in[a_0,a),\ \lambda_c>0\bigr]\\
\Longrightarrow\ \exists b\in(a_0,a):\quad
\eta(a,b)>0\ \land\ \|A_b^{-1/2}J_{a,b}^{\rm src}C_{a,b}^{-1/2}\|<1.
\end{gathered}} \tag{C22}
\]
Every operator, domain and source term in C22 has now been fixed. This assertion is **unproved**. Relative to this reduction it is exactly the strict inequality needed to contradict contact, not an independently available theorem. The new information is bounded explicit cross coupling, a diverging positive collar floor, and a compact norm-one equality case; it is not a claim that algebra has reduced the logical difficulty of the global sign.

### 3.4 The attempted quantitative estimate, and its actual first failure

The first bound tried is
\[
\|\mathcal K_{a,b}\|^2\le\frac{M_a^2}{\lambda_b\eta(a,b)}. \tag{C23}
\]
It is valid but does not prove C22. At a putative contact, \(\lambda_b\downarrow0\) as b increases to a. There is no lower bound for the product \(\lambda_b\eta(a,b)\) supplied by continuity. In fact C21 proves that every valid such split at contact has \(\|\mathcal K_{a,b}\|=1\), hence necessarily
\[
\lambda_b\eta(a,b)\le M_a^2.
\]
Thus a successful proof must use structure in the *coupled* response, rather than declare the diverging collar diagonal sufficient. Failure of the sufficient right side of C23 is not evidence that the source contraction is false away from contact.

There is a further exact source constraint. For a contact kernel vector \(v=u+w\), local nullity gives
\[
Q[u]=Q[w]=-B(u,w),\qquad
\|w\|_2\le\frac{M_a}{\eta(a,b)}\|u\|_2,
\qquad
\lambda_b\le\frac{M_a^2}{\eta(a,b)}. \tag{C24}
\]
The middle relation follows from C20 and the cross bound, and the last from positivity on the core. The boundary mass therefore tends to zero at least at this logarithmic upper rate. It need not be zero. This explicitly exhibits why “small tails” and a strong collar floor still leave the equality case unpaid.

**Q2 closeout:** the initial continuation step is not justified; the concrete core/collar repair proves C14-C24 but leaves C22. No source-compatible first-contact vector was constructed, and none was excluded. E5 refutes only the structure-only shortcut.

## 4. Q3 — exact transfer to the consumer, with the missing premise visible

[COFINAL_FAMILY][CONDITIONAL for C22; PAPER for all displayed implications]

The complete conditional chain is
\[
\begin{array}{c}
\text{C4-C11: actual closed forms, attained continuous bottom, positive anchor}\\
+\ \text{C19-C21: exact positive-core / positive-collar transfer}\\
+\ \text{C22: strict full-source coupling estimate, UNPROVED}\\
\Downarrow\\
\text{no first nonpositive window}\\
\Downarrow\\
\lambda_a>0\quad\forall a>0\\
\Downarrow\\
Q[f]\ge0\quad\forall f\in C_c^\infty(\mathbb R;\mathbb C)\\
\Downarrow\\
\text{the published Weil-criterion consumer is supplied.}
\end{array}
\]
For any fixed complex compact smooth f, choose a containing its support and use its Rayleigh bound. For a below the anchor use nested-window monotonicity. No uniform positive gap as a tends to infinity is required. Both parity sectors, both physical boundaries and both internal cuts are included. No normalization of the raw theta profile enters this chain.

The source expression C1 agrees with the primary Weil functional after conversion from its linear-first convention and the identity
\(2\int_0^\infty\alpha(t)(1-e^{-t/2})dt=\log2+\pi/2\).
This elementary integral gives the precise change from \(\gamma+\log(4\pi)\) to \(c_A\); the primes and both poles are unchanged. Suzuki's actually read HTML introduction states the all-complex compact-smooth criterion. No unverified v2 theorem, imported 0.8 certificate or RH-dependent prime error is used.

| Supplier | Domain / quantifiers | Input -> output | Proof / status |
|---|---|---|---|
| C2-C7 | Every fixed a>0; complex \(V_a\), physical L2 | Literal source -> closed semibounded form, compact resolvent, attained bottom | PAPER; section 1 |
| C8-C10 | Every a>0 and every real sequence tending to it | Fixed source, common dilated domain -> continuous bottom and exact weak equation | PAPER; section 1.4 |
| C11 | One fixed explicit \(a_0=e^{-20}/2\) | Prime-free small window -> \(\lambda_{a_0}>2\) | PAPER; section 1.5 |
| C14-C18 | Every fixed a,d>0; \(v\in\ker A_a\) | Full exterior defect -> collar injectivity and immediate negative enlargement if v is nonzero | PAPER; not a kernel exclusion |
| C19-C21 | \(0<b<a\), \(\lambda_b>0\), \(\eta(a,b)>0\) | Exact core/collar partition -> compact sign classifier | PAPER; positivity hypotheses explicitly discharged only as stated |
| C22 | Every hypothetical first-contact a | Full coupled source -> strict contraction | CONDITIONAL; not proved |
| Consumer transfer | Every complex compact smooth test | C22 plus preceding suppliers -> nonnegativity | PAPER implication; premise remains unpaid |

**FIRST_FAILURE Q3:** C22, not the form-domain transfer or a missing parity assumption. `LOWER_SIGN_PROVED: false` remains mandatory.

## 5. Adversarial test and strongest surviving objection

### 5.1 E5, evaluated exactly

[FINITE_CELL][PAPER]

For the supplied matrix
\[
A_\varepsilon=\begin{pmatrix}0&0&\varepsilon\\0&0&-1\\\varepsilon&-1&0\end{pmatrix},
\qquad 0<\varepsilon\le1,
\]
direct multiplication gives
\[
A_\varepsilon(1,\varepsilon,0)^T=0,
\quad A_\varepsilon e_1=\varepsilon e_3,
\quad \det(tI-A_\varepsilon)=t(t^2-1-\varepsilon^2).
\]
Thus the local compression on \(\mathbb Ce_1\) is zero and nonnegative, its radical projections are onto, the selected tail has norm \(\varepsilon\), but
\[
B(e_3,e_1)=\varepsilon,\quad B(\varepsilon e_2,e_1)=0,
\quad Q_\varepsilon(0,1,1)=-2.
\]
The repaired interpretation passes the falsifier: it reports a nonzero exterior response and a negative enlarged-space trial,
\(Q_\varepsilon(e_1-te_3)=-2t\varepsilon<0\) for t>0. It **does not** report absence of the local kernel.

No proved new source hypothesis in this verdict licenses a global sign conclusion for E5. In particular E5 has no logarithmic Fourier symbol, spatial translations with infinitely many independent translates, shrinking physical collars, or prime/pole cross operator C19. It also does not provide a strictly positive smaller-window core to which C21 could be applied. The new source structural lemmas cannot be transplanted to this finite matrix by analogy. Even for the actual source, they stop before C22. E5 changes its form with \(\varepsilon\); it is not a first-contact counterexample for a fixed nested source.

### 5.2 Scope of the failures

[ABSTRACT][PAPER]

The refuted theorem shape is “nonnegative local compression + onto interior radical projection + small radical tails imply zero exterior coupling.” E5 has all those inputs and coupling \(\varepsilon\ne0\). Its exact evidence is E5 in the pinned E file and section 5.1 above. This is a THEOREM_SHAPE counterexample, not ROUTE_FAMILY death.

The attempted assertion “a boundary collar with a diverging positive diagonal automatically prevents contact” lacks the mixed response estimate. C21-C24 are the precise repair. No claim is made that a finite failure of the bound C23 refutes C22.

The strongest objection to a premature complete verdict is decisive: C18 is exactly what a sign-changing spectral crossing is allowed to do. The argument has not shown why the literal source cannot make that crossing. Neither analyticity of just the geometric exterior part nor a positive Riesz norm supplies the missing strict inequality.

## 6. Route map and consumer-first contract

[ABSTRACT][PAPER for the proved reductions][CONDITIONAL for the open estimates]

| Representation | Preserved / dropped | Kill-power / cost estimate | Status |
|---|---|---|---|
| Coupled two-collar transfer \(\mathcal K_{a,b}\) | Full source, complex class, exact physical norms; no terms dropped | 9/10 / 6/10 | Selected; compact classifier proved, strict contraction unpaid |
| Exterior defect and translation rigidity C14-C18 | Both collars, endpoint capacity, full prime shifts and poles | 9/10 / 3/10 for detecting a wrong continuation argument | Injectivity and immediate crossing proved; no no-contact theorem |
| Signed ground-state transform GS/DOM | Correct only with its signed measure retained | 8/10 / 8/10 | Existing alternative, not reopened or claimed new |

The estimates rank proposed proof work, not probabilities, numerical evidence or execution grants.

```yaml
K8A:
  DOWNSTREAM_CONSUMER: published_Weil_criterion_on_all_complex_compact_smooth_tests
  ACTUAL_CONSUMER_REQUIREMENT: Q_nonnegative_on_every_complex_compact_smooth_test
  ORIGINAL_REQUESTED_OBJECT: first_contact_source_kernel_exclusion
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  EXPLANATION: sufficient_interface_not_a_mandatory_route_for_every_sign_proof
  KNOWN_WEAKER_INTERFACES:
    - direct_all_test_nonnegativity
    - all_large_window_lower_envelope_lambda_ge_minus_epsilon_with_epsilon_to_zero
  EXACT_SELECTED_IMPLICATION: C22_plus_C4_C11_C19_C21_implies_all_test_nonnegativity
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: explicit_Carleman_collar_coupling_endpoint_capacity_and_compact_equality_case
  REOPEN_TRIGGER: independent_full_source_strict_coupling_bound_or_another_complete_sign_identity
SCOPED_REFUTATION:
  CLAIM: local_radical_tail_orthogonality_and_smallness_force_exterior_nullity
  KILL_SCOPE: THEOREM_SHAPE
  KILL_EVIDENCE_KIND: exact_E5_nonzero_exterior_coupling
  EVIDENCE: pinned_E_file_E5_and_this_section_5_1
  FAILURE_TYPE: COUNTEREXAMPLE
  EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
  THETA_TARGET_REFUTED: false
CLOSES:
  - first_contact_analytic_prerequisites_for_the_literal_source
  - endpoint_inclusive_exterior_defect_domain
  - compactly_supported_global_radical_uniqueness
CARRIES_OPEN:
  - first_contact_source_kernel_exclusion
  - all_test_lower_sign
OPENS: []
```

The contraction remainder is an explicit representation of the existing sign obligation, not an additional independent supplier counted as a new opening. No claim of priority in the literature is made.

## 7. Frozen predictions and closeout

[ABSTRACT][PAPER; prediction accounting, not independent verification]

| Frozen prediction | Fate | Evidence |
|---|---|---|
| P1, 0.90: E1-E5 and D20 lineage survive | CONFIRMED | C1, C8-C9, C12-C13 and exact E5 calculation; no source coefficient or sign correction |
| P2, 0.95: automatic tail relations do not exclude first contact | CONFIRMED | E4 rederived; C17 requires exterior vanishing as an additional input; C18 does not supply that input |
| P3, 0.80: partial result with a new source lemma or exact refutation | CONFIRMED | New C14-C24, especially endpoint-inclusive collar bound, C17 and compact classifier; C22 remains unpaid |

No probability or event definition was repaired after the proof attempt. No old numerical forecast, finite source row or SATURATION estimate was rescored.

What became more precise is the equality case: a compact full-source transfer between a positive core and positive thin collars must attain singular value exactly one at contact. What was eliminated is the claim that automatic radical-tail tests see every exterior direction. What must not recur is using positivity on a larger window to prove that no first crossing exists, or replacing the actual coupled inverse in C21 by a purported uniformly positive cofinal floor.

```yaml
iteration:
  target: GOAL058_FIRST_CONTACT_SOURCE_KERNEL_EXTERIOR_RIGIDITY
  status: OPEN
  progress_class: REPRESENTATION_PROGRESS
  cognitive_operator_used: REPRESENTATION_SHIFT
  failed_strategy: infer_exterior_vanishing_from_E4_or_from_a_large_collar_diagonal
  new_gap_name: strict_full_source_collar_contraction_C22
  invariant_learned: nonzero_exterior_response_proves_crossing_not_no_contact
  forbidden_future_move: erase_the_positive_core_resolvent_or_its_mixed_source_coupling
  next_decisive_test: CONTACT_COUPLED_COLLAR_CONTRACTION
  route_score: 3
```

## 8. Exactly one next_decisive_test and verification handoff

**CONTACT_COUPLED_COLLAR_CONTRACTION.** This is a paper/validated-operator discriminator for the new first failure, not a request for another old scalar run.

Objects: the fixed source C19, a candidate first-contact a, a smaller positive core b with the explicit \(\eta(a,b)>0\), and the compact operator \(\mathcal K_{a,b}\). Terminal observable:
\[
\boxed{\Delta(a,b)=1-\|\mathcal K_{a,b}\|^2.} \tag{C25}
\]
The next analytical task is to estimate this **coupled** object before replacing either inverse by its worst eigenvalue. A proof of \(\Delta(a,b)>0\) for at least one admissible b at every hypothetical first-contact a supplies C22. A finite-window estimate supplies only that finite window.

For a bounded verifier, finite-rank compression is legitimate only with a full remainder. For example, let P and R be spectral projections onto the first p and q eigenvectors of the positive core and collar operators, with next eigenvalues \(\mu_{p+1}\) and \(\nu_{q+1}\). Then
\[
\|\mathcal K-P\mathcal K R\|
\le M_a\left((\mu_{p+1}\eta(a,b))^{-1/2}
+(\lambda_b\nu_{q+1})^{-1/2}\right).
\]
This follows by writing \((I-P)\mathcal K+P\mathcal K(I-R)\). It is a conditional verifier bound, not supplied numerical spectral data or an authorization to compute unknown ground vectors. Other source-certified projections and tail bounds may replace it with an explicit same-object proof.

**Threshold and stopping condition:** admit a positive-window conclusion only from a rigorous strictly positive lower enclosure of C25. A strictly negative upper enclosure gives a negative window through C21; it contradicts a claimed nonnegative-contact classification, not automatically the whole source theorem. An enclosure containing zero is UNRESOLVED. The exact-zero discriminator is the coupled equality system
\[
A_bu=J_{a,b}^{\rm src}w,\qquad
C_{a,b}w=(J_{a,b}^{\rm src})^*u,\qquad (u,w)\ne(0,0),
\]
whose solution gives the actual local kernel vector \(w-u\). Do not label a tiny singular-value gap nonzero without separating it from one. Stop the absolute-majorant subattempt if it supplies only C23 with a right side at least one: this kills that estimate, not the contraction target. Do not enlarge a, a projection dimension, or numerical precision merely to conceal that failure.

**One Codex handoff:** independently audit C14-C24, in particular endpoint removability, the half-Carleman coefficient, the bounded sharp split and all three directions of the sign classifier; then attack the same coupled observable C25. Required output is the first exact failed identity or a proof/certificate with its complete operator tail. This verdict authorizes no Lean, queue, registry, state or old-verdict edits.

**Publication gate:** only the expected verdict path is written. Verify the resulting one-path commit, fetch the file at that commit, and match its Git blob to the local UTF-8 artifact. The external receipt gives the actual commit and exact artifact hash/counts because inserting a file's own hash or its enclosing commit into its bytes is self-referential. No `lake` gate or axiom profile is claimed: no Lean source was written. Independent mathematical review remains pending after publication.

## 9. Proshka's own line

I keep the literal source operator rather than a substitute positive norm.
The collar calculation uses the part of the equation that local tests do not observe.
Both exterior sides matter for a general complex vector.
A single analytic geometric tail is not the full arithmetic tail.
The prime shifts remain rough enough that analytic continuation cannot be asserted by inspection.
The first alternative was completeness of the already known radical tails.
Those relations are automatic, so their number does not measure additional information.
The second alternative was the positive-profile ground-state transform.
Its signed jump measure has already failed the proposed positivity test.
I have not repackaged that old failure as a new mechanism.
The useful surprise is that the adjacent archimedean coupling is bounded on physical L2.
Its singularity is Carleman, not an uncontrolled endpoint trace.
That fact also gives a direct proof that the internal sharp cuts preserve the form domain.
The thin collars have a large positive diagonal without any global sign assumption.
But their positive diagonal is not the final budget.
The actual core response must be subtracted before any conclusion is possible.
One move beyond this batch is to control that coupled response without its worst inverse norm.
It fails as a shortcut if every estimate first spends the collapsing core eigenvalue.
Another move is to analyze the equality system through the exact two-sided defect.
It fails if it silently assumes positivity in a window larger than the contact window.
The most useful requested object would be a rigorous source-bound for the normalized cross operator.
Another table of the old theta upper-trial energies would not answer this question.
For any operator computation I would require the off-diagonal prime and pole errors explicitly.
I distrust claims of a boundary value for an arbitrary logarithmic-domain vector.
I also distrust an exact-zero conclusion inferred from a very small collar response.
The response really tends to zero as the collar shrinks, even when each response is nonzero.
Immediate negative crossing is a genuine result, but it is not a contradiction by itself.
The remaining task is to show why this particular source cannot reach the norm-one coupling.

## 10. Research log

### 10.1 Sources actually consulted

All repository locators below use the complete paths, SHA-256 declarations and blobs in section 0 at SOURCE_BASE; their read/hash limitations remain operative.

| Source / exact locator | READ or RELAY | Use or rejection |
|---|---|---|
| CONTACT request at `4bf7ce2a65c380c6107ba204c75697029fdb8c2f` | READ full; bytes rehashed | Exact source, three questions, supplied E5, frozen predictions and sole write path |
| Bootstrap on `rh_clean`, blob `eba04b799176c9e6a1d5f7fc4061280cfbf96ad4` | READ, including final protocol sections | Source-locked intake, one operative directive, scope and publication requirements |
| E, E1-E5 and audit receipt | READ full; bytes rehashed | Exterior identity, automatic tail relations and algebraic falsifier; independently rederived here |
| H, source distinctions and section 6 / H15-H17 | READ relevant text | First-contact consumer and historical operator/domain distinctions; 0.8 import not spent |
| D, source/domain sections, D14, D20-D21, D36 | READ relevant text | Literal form lineage, weak equation, semiboundedness and prime-free anchor; proofs reconstructed here |
| S, header, A1-A5/domain and upper-rate scope | READ relevant local text; full artifact rehashed | Preserve accepted upper supplier without rerunning A22 or using it as lower sign |
| I, display audit, source limits and final transfer | READ; independent acceptance is RELAY | Record accepted upper-rate status and June-PDF versus later-HTML limitation |
| X, source register, (Q), (X), (CONT), signed-transform scope | READ relevant text | Full source and negative-measure warning; no new GS/DOM attempt claimed |
| J, sections 0-2 | READ; numerical audit is RELAY | Raw normalization factor and signed GS/prime-free negative interval; no rerun |
| B, complete 79-line file | READ; bytes rehashed | Proof-batch, own-line and research-log format |
| Suzuki, *Weil's quadratic form via the screw function*, `https://arxiv.org/html/2606.09096v1`, introduction and displayed Weil functional | READ primary HTML | Functional and all-complex compact-smooth criterion; v1 header / August 24 body date explicitly retained; not local-PDF or v2 verification |
| Web search for logarithmic-operator / Suzuki context | Search snippets screened, not theorem imports | Secondary summaries and different logarithmic-Schrodinger models do not establish the literal prime-shift continuation theorem |
| Uploaded-file CONTACT search | Retrieval only | Returned unrelated historical project excerpts; no replacement request or mathematical premise selected from them |
| Exact raw-GitHub HTTP acquisition attempts | FAILED transport, not READ evidence | Runtime network/cache acquisition did not yield source bytes; connector pins remain authoritative |

No external unique-continuation theorem, RH-dependent prime estimate, PDF theorem, numerical eigenvalue or new concentration theorem was imported. The Fourier, Hilbert-space, compact-operator and finite-support distribution facts are used with their stated hypotheses and the necessary local proofs above. This log does not claim a literature priority or absence theorem.

### 10.2 Attempted representations and first obstacles

| Candidate | First obstacle and disposition |
|---|---|
| Automatic Bessel-tail equations force all exterior defects zero | E4 has no exterior completeness premise; exact E5 refutes the structure-only implication |
| Analytic continuation of the geometric exterior series alone | Prime-shift contribution is only locally L2; continuing a summand is not continuing the source equation |
| Vanishing collars imply compact-radical uniqueness | Survives after C16 removes both endpoint-supported defects; C17 proves the implication |
| Nonzero collar response contradicts first contact | False inference: C18 gives negative larger windows, precisely what a crossing permits |
| Large positive collar diagonal dominates everything | Actual core recovery remains; C23 cannot supply strictness without a product lower bound |
| Replace full coupling by a prime-only norm | Wrong operator: C19 and C21 retain the archimedean and both pole terms plus their mixed recovery |
| Reuse the signed positive-profile transform | Not pursued as new work; its nonnegative-measure claim is already refuted in X/J |
| Import the historical 0.8 certificate or fresh Suzuki continuity wholesale | Unneeded: C4-C11 prove the actual domain, continuity and an explicit small anchor directly |

### 10.3 Reusable intermediate results and their limits

C10 gives an L2-bounded change of the Dirichlet energy under dilation, while prime translations need only strong continuity plus compactness.
C14-C15 bound the literal exterior defect up to each boundary by a half-Carleman operator plus explicit bounded source terms.
C16 rules out endpoint Dirac defects in the actual local E dual without assigning a point value to v.
C17 proves two-sided collar injectivity and compact-support global-radical uniqueness using exact translations and compact resolvent.
C18 constructs a negative larger-window trial from any nonzero local kernel; it cannot establish nonexistence of that kernel.
C19 supplies a bounded physical-L2 cross operator even across touching core/collar boundaries.
C20 is an unconditional diverging collar floor, not a full-window floor.
C21 classifies the full window by one compact normalized coupling, with the equality case attained.
C23-C24 locate the failed absolute bound and give necessary contact constraints, not a lower-sign proof.
C22 is the only unproved source estimate retained for this chosen mechanism.
