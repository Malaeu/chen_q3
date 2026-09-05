# STATUS: TRY_DOMFM_ZERO_MARGIN_COUPLED_CERTIFICATES
```yaml
OPERATIVE_CLASS: TRY_DOMFM_ZERO_MARGIN_COUPLED_CERTIFICATES
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-05-DOMFM
BOUNDARY_ID: GOAL058_DOM_FM_AT_ZERO_MARGIN_WITH_MARGIN_DENSITY_TRADEOFF
RESULT: PARTIAL_PROOF_WITH_PRECISE_REMAINDER
REQUEST_LOCK:
  COMMIT: 554ce54ea0b72a07e4064aec14ec36a55642b60c
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_DOM_FM_ZERO_MARGIN_AND_TRADEOFF_LEMMA_2026-09-05.txt
  GIT_BLOB: f4721b32ce4e0d9e865ded689a05ac6cffd9935c
  SHA256: afbc2a4eb7ed290f7c125f11e89b13905a7b13955e98ae9a4e0f88d84dd288ca
  BYTES: 8166
  LINES: 82
  FINAL_LF: true
  SHA256_AND_GIT_BLOB_RECOMPUTED: true
SOURCE_BASE_REF: 149f6af5
BOOTSTRAP_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_DOM_FM_ZERO_MARGIN_AND_TRADEOFF_LEMMA_2026-09-05.md
ADMISSION:
  DELIVERY: OWNER_EXACT_GITHUB_REQUEST_LOCATOR
  AUTOMATED_REVIEW_PLAN_EXECUTION_VERIFIED: false
  REQUEST_OR_QUEUE_REBOUND: false
CLOSES: []
OPENS: []
CANONICAL_RH_SUPPLIER_COUNT_DELTA: 0
CLOSED_PAPER_REVIEW_OBLIGATIONS:
  - D1_SHARP_PROJECTION_TRADEOFF_WITH_NONZERO_PROJECTION_GUARD
  - D1_FORM_DENSITY_OBSTRUCTION_WITH_QUADRATIC_ERROR_BUDGET
  - D2_EXACT_SECOND_VARIATION_AND_REGULARIZED_KERNEL
  - D2_ALL_POSITIVE_WEIGHT_ABSOLUTE_SCHUR_OBSTRUCTION
  - D3_COMPRESSED_GAP_GRAM_AND_SAME_FAMILY_RECOVERY
D1_SOURCE_REPAIRS:
  PROJECTION_MUST_BE_NONZERO: true
  FINITE_OPERATOR_NORM_IS_L2_OPERATOR_NORM: true
  DENSITY_TOPOLOGY: X_FORM_CONTROL_NOT_BARE_L2
  HISTORICAL_2025_FUNCTIONAL_EQUALS_CANONICAL_Q: NOT_ESTABLISHED_AND_NOT_ASSUMED
D2:
  UNREGULARIZED_POINTWISE_DIAGONAL: LOGARITHMICALLY_DIVERGENT
  DIFFERENCE_FORM: WELL_DEFINED
  ABSOLUTE_SCHUR_ALL_POSITIVE_REWEIGHTINGS: EXCLUDED
  ACTUAL_DOM: NOT_PROVED
D3:
  FINITE_CELL_FULL_GAP_EQUIVALENCE_REQUIRES_FULL_RANGE: true
  COFINAL_EQUIVALENCE_REQUIRES_PROVED_FIXED_TEST_RECOVERY: true
  VANISHING_LOWER_ERROR_SUPPLIER: NOT_PROVED
SCOPED_KILLS:
  - CODE: KILL_UNIFORM_POSITIVE_MARGIN_ON_FORM_DENSE_FAMILY
    KILL_SCOPE: THEOREM_SHAPE
    FAILURE_TYPE: INCOMPATIBILITY
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
    KILL_EVIDENCE_KIND: STRICT_NEGATIVE_UPPER_BOUND_ON_CLAIMED_MARGIN
    EVIDENCE: THIS_DOCUMENT_D1_EQUATION_MARGIN_KILL
  - CODE: KILL_ABSOLUTE_SCHUR_ALL_POSITIVE_WEIGHTS
    KILL_SCOPE: THEOREM_SHAPE
    FAILURE_TYPE: INCOMPATIBILITY
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
    KILL_EVIDENCE_KIND: EXACT_STRICT_NEGATIVE_INTEGRATED_DEFECT
    EVIDENCE: THIS_DOCUMENT_D2_EQUATION_SCHUR_KILL
ACTUAL_WEIL_FORM_REFUTED: false
ROUTE_FAMILY_MATHEMATICALLY_DEAD: false
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
LEAN_SOURCE_WRITTEN: false
LEAN_KERNEL_RUN: false
NUMERICAL_EXPERIMENT_RUN: false
ARISTOTLE_SUBMISSION: false
OLD_VERDICT_OR_SHARED_STATE_CHANGED: false
PHASE_KEY_CHANGED: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## Source boundary and result

This is a **partial paper proof**, not a proof of (DOM), (FM), or RH. Besides the requested tradeoff, the new decisive result is stronger than failure of one guessed Schur weight: **no positive diagonal reweighting can make the absolute-value Schur test work for the exact cutoff canonical interaction kernel**. A positive-semidefinite three-vertex plant proves that this obstruction does not establish negativity of the original form.

The request and GitHub file blob agree. The fetched UTF-8 content was materialized locally; SHA-256, Git-blob SHA-1, byte count, line count, and final LF were recomputed. Computation in this adjudication is file verification, not a mathematical numerical experiment.

**Pinned sources.** References below mean the following exact sources, not newer repository results.

- **[R]** The request at its commit/path/blob in the header.
- **[X]** `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_WEIL_POSITIVITY_AROUND_XI_PROOF_2026-09-05.md` at `149f6af5`, blob `136aceb3cbbabcdfa425459562b803b67c548b48`. The complete 796-line local copy was read and its SHA-256 recomputed as `93db2de6357821918211a8033b2c8f34e7f684320a25e5623e1f24d33ed58fe9`; GitHub confirms the same blob at the pinned ref.
- **[A]** `docs/routeB_bus/AGENT_REPORT_2026-09-05_GOAL058_XIDEV_INDEPENDENT_AUDIT.md` at `149f6af5`, request-reported SHA-256 prefix `b2914990a93020bf`. Its independent re-derivations were read. Its numerical checks are reported evidence, not premises. In particular its four SURVIVES judgments do not upgrade PAPER to LEAN.
- **[G]** `q3.lean.aristotle/Q3/Proofs/RouteB/WeilGramMinusShift.lean` at `149f6af5`, blob `5343f3001580c22c19a9e5bb1d0a7ba9518f06a9`. The source explicitly limits itself to finite quadratic algebra, without the integral term or analytic CCM crosswalk.
- **[F]** `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrix.lean` and its direct entry-constructor import `CCMFiniteWeilSourceMatrixN1.lean`, both at `149f6af5`, blobs `972223c3f3a93d1ccab750086de0eb467bb74efa` and `960f1de9d00e9ca4b309a99fe98be48db40cdb31`. The carrier, full entry constructor, and component definitions were read.
- **[M]** `q3.lean.aristotle/Q3/Proofs/RouteB/MangoldtDivisibilityEnergy.lean` at `149f6af5`. The inspected source proves finite divisibility algebra and uses the constant `log 4 + 4`, not the sharper paper constant `4 log 2`. Neither gives (DOM).
- **[D]** `docs/routeB_bus/phase5_codex/overlap_dictionary.py` at `149f6af5`, blob `ba413747f357d2abcab2a696abe464dd02a7f83e`. Read, not run.
- **[H]** `docs/routeB_bus/litreview/MALAMUTMANN2025_Q3_USAGE_CARD.md` at `149f6af5`, request-reported SHA-256 prefix `a507457f114f42f2`. Historical statements below are attributed to this pinned transcription. The original 2025 PDF was not independently re-audited here.
- **[C]** Connes–Consani–Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1, (2.6), (3.5)–(3.11), §4. **[W]** Connes–Consani, *Spectral Triples and Zeta-Cycles*, arXiv:2106.01715v1, (1.1)–(1.2), §2.1.1. Their primary HTML texts were consulted. These supply definitions and the explicit-formula/Weil-criterion theorem, not the missing positivity estimate.

Only the request and [X] full hashes are claimed recomputed. Other listed source prefixes are provenance supplied by [R], not silently recertified hashes. All new lemmas below have verifier **PAPER**. Lean heads are mathematical implementation specifications, not compiled declarations. Novelty relative to the literature is not claimed.

## D1. The margin–density tradeoff, with its necessary guards

### Lemma D1.1 — sharper finite-dimensional tradeoff [FINITE_CELL][PAPER]

Let E be a finite-dimensional complex Hilbert space, K a self-adjoint operator on E, V a subspace, and y nonzero. Write p for the orthogonal projection of y onto V. Assume **p is nonzero**. Put
\[
 d=\frac{\|y-p\|}{\|y\|}<1,\qquad M=\|K\|_{2\to2},\qquad
 R_K(y)=\frac{\langle y,Ky\rangle}{\|y\|^2}.
\]
Rayleigh values are real. Then
\[
 \boxed{\lambda_{\min}(K|_V)\le R_K(p)
 \le R_K(y)+2Md
 \le R_K(y)+2Md+Md^2.}                         \tag{TRADE}
\]
For a basis synthesis matrix Z of V, the left-hand side is the generalized minimum of \((Z^*KZ,Z^*Z)\). With redundant columns use the quotient by \(\ker Z\); do not invert a singular Gram matrix.

**Proof.** Set \(u=y/\|y\|\) and \(v=p/\|p\|\). Orthogonal projection gives
\(\langle u,v\rangle=\|p\|/\|y\|=\sqrt{1-d^2}\), a nonnegative real number. Self-adjointness gives
\[
 R_K(p)-R_K(y)=\Re\langle v-u,K(v+u)\rangle.
\]
Moreover
\[
 \|v-u\|^2\|v+u\|^2
 =(2-2\sqrt{1-d^2})(2+2\sqrt{1-d^2})=4d^2.
\]
Cauchy–Schwarz and the operator norm prove the absolute bound \(|R_K(p)-R_K(y)|\le2Md\). The minimum on V is at most its value at the unit vector v. The last inequality uses \(M,d^2\ge0\). This proof does not omit a denominator: both compared vectors were normalized before estimating. □

**Boundary checks.** If \(p=0\), the requested projected Rayleigh quotient is undefined; \(y=e_1,V=\mathbb Ce_2\) is an exact example. If K varies with the family, \(d_j\to0\) alone does not imply \(M_jd_j\to0\). No global bounded \(\|Q\|_{L^2\to L^2}\) is asserted for the Weil form.

**Lean-ready head.** For `E := EuclideanSpace ℂ (Fin n)`, use `K : Matrix (Fin n) (Fin n) ℂ`, `K.IsHermitian`, and its induced continuous linear map `Kop : E →L[ℂ] E`. Specify the coefficient identity between Kop and K explicitly. With `V : Submodule ℂ E`, `y p : E`, hypotheses `y ≠ 0`, `p ≠ 0`, `p ∈ V`, and `∀ v ∈ V, ⟪v, y-p⟫_ℂ = 0`, the head `domfm_projected_rayleigh_le` concludes the middle inequality of (TRADE). Here `M := ‖Kop‖`; an entrywise matrix norm is not substituted. The variational corollary `domfm_restricted_min_le_projected_rayleigh` uses the infimum over unit vectors in V. The projection witnesses avoid dependence on an unverified projection API spelling.

### Lemma D1.2 — eigenvector and radical improvement [FINITE_CELL][PAPER]

If \(Ky=\lambda y\), then
\[
 R_K(p)-\lambda
 =\frac{\langle y-p,(K-\lambda I)(y-p)\rangle}{\|p\|^2},
\quad
 |R_K(p)-\lambda|\le
 \frac{(M+|\lambda|)d^2}{1-d^2}.                 \tag{EIG-TRADE}
\]
In particular for \(Ky=0\), the error is at most \(Md^2/(1-d^2)\), not merely O(d).

**Proof.** Expand \(p=y-(y-p)\) in the form of \(K-\lambda I\). Its terms containing y vanish. Orthogonality gives \(\|p\|^2=(1-d^2)\|y\|^2\); apply \(\|K-\lambda I\|\le M+|\lambda|\). □

A sampled Xi row in a finite CCM cell is not an exact radical vector merely because its Rayleigh value is small. Apply (EIG-TRADE) to it only with a proved eigen-equation. The general bound (TRADE) remains available.

**Lean-ready head:** `domfm_eigenvector_projection_quadratic_error`, under D1.1's hypotheses plus `Kop y = (λ : ℂ) • y`, with both conclusions in (EIG-TRADE).

### Lemma D1.3 — no uniform positive margin on a form-dense family [COFINAL_FAMILY][PAPER]

Use [X]'s control space and actual canonical kernel:
\[
 \begin{split}
 a(t)&=\frac{e^{-t/2}}{1-e^{-2t}},\quad
 \mathcal D(g)=\int_0^\infty a(t)\|g(\cdot+t)-g\|_2^2dt,\\
 \|g\|_X^2&=\|e^{|x|}g\|_2^2+\mathcal D(g),\qquad C_X=|c_A|+14,\\
 h(u)&=(\pi^2u^4-\tfrac32\pi u^2)e^{-\pi u^2},\\
 \Phi(x)&=4e^{x/2}\sum_{n\ge1}h(ne^x),\quad A=\|\Phi\|_2>0,\quad f_0=\Phi/A.
 \end{split}                                                   \tag{OBJECTS}
\]
Here \(c_A=\gamma+\log(8\pi)+\pi/2\). The PAPER inputs [X, domain lemma and L1–L2], independently re-derived in [A], are
\[
 \|f_0\|_2=1,\quad f_0>0,\quad f_0\in X,\quad
 B(f_0,g)=0\ (g\in X),\quad
 |B(g,h)|\le C_X\|g\|_X\|h\|_X.                 \tag{RAD-CONT}
\]
They use the exact explicit formula: \(\mathcal F f_0(z)=\Xi(z)/A\) and every canonical zero-side summand vanishes. They do not use RH or a positivity premise. Compact smooth functions are dense in X.

Let \(v_j\in V_j\subset X\), with each V_j finite-dimensional, and suppose a proved budget gives
\(\delta_j=\|v_j-f_0\|_X\to0\). For \(\delta_j<1\),
\[
 \boxed{\frac{|Q(v_j)|}{\|v_j\|_2^2}
 \le\frac{C_X\delta_j^2}{(1-\delta_j)^2}.}        \tag{FORM-TRADE}
\]
Consequently no fixed \(c>0\) can satisfy \(Q(v)\ge c\|v\|_2^2\) on every sufficiently late \(V_j\).

**Proof.** The radical identity gives the exact equality
\(Q(v_j)=Q(v_j-f_0)\). Apply (RAD-CONT). Since \(\|g\|_2\le\|g\|_X\), the triangle inequality gives \(\|v_j\|_2\ge1-\delta_j\). These prove (FORM-TRADE). For any \(c>0\), eventually
\(\delta_j<\sqrt c/(\sqrt{C_X}+\sqrt c)\), and hence
\[
 \boxed{\lambda_{\min}(Q|_{V_j})-c
 \le\frac{C_X\delta_j^2}{(1-\delta_j)^2}-c<0.}    \tag{MARGIN-KILL}
\]
This is an upper bound refuting the claimed positive margin, not a negative lower bound misread as a counterexample. The same argument applies to a form-dense union carrying the same c, by choosing approximants to \(f_0\). □

For the actual diagonal \(m=N\), [X, (REC-BUDGET)] supplies such \(v_m=P_{\log m,m}f_0\). D1 improves the previous linear continuity estimate to a **quadratic** error budget. In particular
\(\limsup_m\lambda_{\min}(K_{m,m})\le0\).
This is an upper bound only; it does not prove convergence of the bottom to zero or its nonnegativity. Positive margins on a fixed window, or margins depending on the window and tending to zero, are not excluded.

**Why bare L² density is insufficient.** On \(\ell^2(\mathbb N_0)\) take
\(Q_*(x)=\sum_{n\ge1}n^2|x_n|^2\), with its energy domain, and radical vector \(e_0\). Let V be the finite sequences satisfying \(x_0+\sum_{n\ge1}x_n=0\). Since \(\sum n^{-2}\le2\),
\(\|x\|_2^2\le3Q_*(x)\) on V. Yet V is L² dense: correct the sum of any finite sequence by spreading its negative equally over N unused coordinates; the correction norm tends to zero. Thus L² density can coexist with a uniform positive margin when energy convergence fails. This exact plant prohibits the unqualified density wording in [R].

**Lean-ready heads:** `domfm_radical_approximation_quadratic_budget` on a normed control space X with continuous B and an explicitly bounded inclusion into L²; `domfm_no_uniform_positive_margin_of_form_approximation` with (RAD-CONT), \(\delta_j\to0\), and conclusion (MARGIN-KILL) eventually for each \(c>0\). These are not heads assuming a globally bounded Weil operator on L².

### Historical consequence: repair the object attribution [ABSTRACT][PAPER]

The same-form theorem in D1.3 excludes the proposed uniformly positive, form-dense repair of OPEN-OVERLAP. It also excludes **any** historical closure satisfying those exact same-form, same-norm, form-density hypotheses, independently of the size of its positive constant.

But [H] explicitly says that the 2025 paper's linear functional \(F(\varphi)\), pointwise-positive cone, RKHS norm, and matrix are not yet identified with the canonical quadratic Q and its norm. Therefore the stronger statement “D1 alone directly contradicts that literal operator inequality” is **not established**. A failed identification cannot be assumed in order to refute the source.

There is a separate, exact counterexample to the broad-cone positivity conclusion **for the formula transcribed in [H, cards 1–2]**:
\[
 F(\varphi)=\int a^*(\xi)\varphi(\xi)d\xi
       -\sum_{n\ge2}\frac{2\Lambda(n)}{\sqrt n}\varphi(\xi_n),
 \quad \xi_n=\frac{\log n}{2\pi}.
\]
Let \(\tau=\xi_2>0\), fix \(t>0\), and set
\[
 \varphi_B(\xi)=\frac{
 (1-|\xi-\tau|/B)_+\rho_t(\xi-\tau)
 +(1-|\xi+\tau|/B)_+\rho_t(\xi+\tau)}{\rho_t(0)},
 \quad \rho_t(x)=(4\pi t)^{-1/2}e^{-x^2/(4t)}.
\]
Choose a fixed neighborhood of \(\pm\tau\) on which \(|a^*|\le M_*<\infty\), then \(B>0\) small enough to stay inside it and \(B<\tau/2\). This is a positive multiple of [H]'s own cone generator. Its value at \(\tau\) is 1 and its integral is at most \(2B\), because the Gaussian ratio is at most 1 and each triangle has integral B. All other prime terms are nonpositive after subtraction. With \(w_*=2\log2/\sqrt2>0\),
\[
 F(\varphi_B)\le2M_*B-w_*\le-w_*/2<0
 \quad\text{when }2M_*B\le w_*/2.                \tag{LEGACY-PLANT}
\]
Local boundedness follows from the transcribed digamma density on a compact neighborhood. No numerical table, no sign of the full archimedean density, and no RH premise is used. This refutes that broad-cone positivity statement as transcribed; it does not replace the canonical Weil form by the legacy functional. A conditional theorem listing several hypotheses is not refuted merely because their intended simultaneous instantiation fails.

**Lean-ready head:** `domfm_atomic_sampling_defeats_broad_positive_cone`, for a locally bounded density and a positive sampling atom, with the explicit triangular-Gaussian witness and upper bound (LEGACY-PLANT). Historical source attribution remains a PAPER transcription dependency.

## D2. Exact second variation and the canonical-weighted kernel

### Lemma D2.1 — the second variation is exactly quadratic [ABSTRACT][PAPER]

Set
\[
 k(t)=\frac{e^{-5t/2}}{1-e^{-2t}},\quad b(t)=k(t)-e^{t/2},\quad
 w_n=\frac{\Lambda(n)}{\sqrt n},\quad
 E_s(t)=\int f_0(x)f_0(x+t)|s(x+t)-s(x)|^2dx.
\]
For \(s\in C_c^\infty(\mathbb R;\mathbb C)\), define
\[
 D(s)=\int_0^\infty b(t)E_s(t)dt+\sum_{n\ge2}w_nE_s(\log n).
\]
Then, for every \(\alpha\in\mathbb C\),
\[
 \boxed{E_{1+\alpha s}(t)=|\alpha|^2E_s(t),\qquad
 Q(f_0(1+\alpha s))=|\alpha|^2D(s),\qquad D(s)=Q(f_0s).}       \tag{SECOND}
\]
For real epsilon the second derivative is \(2D(s)\); there is no cubic remainder.

**Proof.** Constants disappear in the difference. This proves the first equality. For completeness, the signed ground-state identity follows by subtracting \(\Re B(f_0,f_0|r|^2)=0\) from \(Q(f_0r)\). Pointwise, for positive p,q and complex u,z,
\[
 |qz-pu|^2-(q-p)(q|z|^2-p|u|^2)=pq|z-u|^2.
\]
The pole and prime correlations have difference \(-pq|z-u|^2\). In the full source form the coefficients are therefore
\(a-e^{-t/2}-e^{t/2}=b\) and \(+w_n\), while the scalar diagonal cancels. This proves (GS) and hence (SECOND). The functions multiplied into \(f_0\) are bounded with bounded derivatives and constant outside a compact set. Near zero \(E_s(t)=O(t^2)\); at infinity the canonical factors decay faster than every exponential. These facts justify all integrals and the subtraction. □

**Lean-ready head:** `domfm_canonical_second_variation (s : ℝ → ℂ) (α : ℂ)`, with `ContDiff ℝ ⊤ s`, `HasCompactSupport s`, and the three exact equalities in (SECOND), based on the proved radical identity rather than a minimum assumption.

### Lemma D2.2 — explicit kernel and its diagonal [ABSTRACT][PAPER]

First regularize at \(0<\epsilon<\min(1,\log2)\). For fixed x define the signed off-diagonal row measure
\[
 \begin{split}
 J_\epsilon(x,dy)={}&f_0(x)f_0(y)b(|y-x|)
       \mathbf1_{|y-x|\ge\epsilon}\,dy\\
 &+f_0(x)\sum_{n\ge2}w_n\bigl[
       f_0(x+\log n)\delta_{x+\log n}(dy)
      +f_0(x-\log n)\delta_{x-\log n}(dy)\bigr].
 \end{split}                                                     \tag{KERNEL}
\]
The product measure \(dx\,J_\epsilon(x,dy)\) is symmetric. Its signed degree is
\[
 \begin{split}
 d_\epsilon(x)=f_0(x)\{&\int_\epsilon^\infty b(t)
        [f_0(x+t)+f_0(x-t)]dt\\
 &+\sum_{n\ge2}w_n[f_0(x+\log n)+f_0(x-\log n)]\}.
 \end{split}                                                     \tag{DIAG}
\]
On compact smooth s put
\[
 T_\epsilon s(x)=d_\epsilon(x)s(x)-\int s(y)J_\epsilon(x,dy).

a_\epsilon(x):=\int |J_\epsilon|(x,dy).
\]
Thus the distribution kernel is \(d_\epsilon(x)\delta_x(dy)-J_\epsilon(x,dy)\), not an ordinary function on the diagonal. Then
\[
 \langle s,T_\epsilon s\rangle_{L^2(dx)}
 =\frac12\iint |s(y)-s(x)|^2J_\epsilon(x,dy)dx
 =:D_\epsilon(s).                                  \tag{PAIR}
\]
All cutoff integrals are finite. The uncut T is defined by the convergent difference expression, not by subtracting two divergent row integrals. Quantitatively,
\[
 \boxed{|D(s)-D_\epsilon(s)|
       \le\frac53\|s'\|_\infty^2\epsilon^2.}        \tag{UV-BUDGET}
\]
For each fixed x its raw degree diverges:
\[
 d_\epsilon(x)=f_0(x)^2\log(1/\epsilon)+O_x(1)
       \quad(\epsilon\downarrow0).                 \tag{UV-DIAG}
\]
There is no finite unregularized pointwise diagonal balance to which one can apply ordinary diagonal dominance.

**Proof.** Pair the two orientations of every continuous edge and every prime shift; symmetry gives (PAIR), including its factor 1/2. Put \(C_0(t)=\int f_0(x)f_0(x+t)dx\). It is positive and at most 1. The derivative bound gives \(E_s(t)\le\|s'\|_\infty^2t^2C_0(t)\). On \((0,1]\), \(|b(t)|\le a(t)+e^{t/2}\le10/(3t)\). Integrating on \((0,\epsilon)\) proves (UV-BUDGET). No prime atom lies there.

The canonical envelope in [X, (ENV)] and its correlation proof give
\(C_0(t)\le C_0^*e^{-t/2}e^{-\pi e^t}\) for an explicit finite \(C_0^*>0\). Hence
\(\int_\epsilon^\infty|b(t)|C_0(t)dt+\sum w_nC_0(\log n)<\infty\).
This also proves absolute integrability of both row masses over x. Finally \(b(t)=1/(2t)+O(1)\) and \(f_0(x+t)+f_0(x-t)=2f_0(x)+O_x(t^2)\). Substitution in (DIAG) proves (UV-DIAG). In the difference expression the factor \(s(x)-s(x\pm t)=O(t)\) makes each local integral convergent. For compact smooth s the canonical decay controls the remaining x and t tails. □

**Norm convention.** Here \(D(s)=\langle s,Ts\rangle\) uses Lebesgue measure. Alternatively, in \(L^2(f_0^2dx)\), multiplication by \(f_0\) is unitary onto L²(dx), and the corresponding formal action is \(f_0^{-2}Ts\). Its form domain is \(\{s:f_0s\in X\}\). Neither formulation declares a globally bounded, positive, or self-adjoint maximal realization without its own operator-domain proof; the quadratic-form statements suffice.

**Lean-ready heads:** `domfm_cutoff_kernel_pairing` for (KERNEL)–(PAIR), `domfm_cutoff_difference_error` for (UV-BUDGET), and `domfm_cutoff_degree_log_asymptotic` for (UV-DIAG). Required objects are Bochner integrals, measures/Dirac measures, `ContDiff`, and the source envelope. These are new analytic definitions to implement, not declarations supplied by [G].

### Lemma D2.3 — Fourier representation is not a scalar multiplier [ABSTRACT][PAPER]

Use \(\widehat s(\xi)=\int s(x)e^{-i\xi x}dx\). Set
\(w_t(x)=f_0(x)f_0(x+t)\), and write
\(d\nu(t)=b(t)dt+\sum_{n\ge2}w_n\delta_{\log n}\) for \(t>0\), as shorthand for the separately convergent weighted integrals and sum; the difference factors keep the integral finite at zero. Define
\[
 \mathcal M(\eta,\xi)=\int_{t>0}
 (e^{-i\eta t}-1)(e^{i\xi t}-1)
       \widehat{w_t}(\eta-\xi)\,d\nu(t).
\]
Then
\[
 \boxed{D(s)=\frac1{(2\pi)^2}
   \iint\overline{\widehat s(\eta)}\,
       \mathcal M(\eta,\xi)\widehat s(\xi)\,d\eta d\xi.}         \tag{FOURIER}
\]
The kernel is Hermitian. Its diagonal is
\[
 \mathcal M(\xi,\xi)=\int_{t>0}|e^{i\xi t}-1|^2 C_0(t)\,d\nu(t).
\]
Neither that diagonal nor the sign of b alone determines positivity of the two-frequency kernel.

**Proof.** Insert Fourier inversion in \(s(x+t)-s(x)\), multiply by its conjugate, and integrate \(w_t(x)e^{i(\xi-\eta)x}\); this is \(\widehat{w_t}(\eta-\xi)\). Near zero the exponential product is bounded by \(|\eta\xi|t^2\); at infinity it is at most 4 and the weighted total variation is integrable by D2.2. These bounds and the Schwartz decay of \(\widehat s\) justify Fubini. Reality of \(w_t\) gives Hermitian symmetry. The nonconstant weight \(f_0(x)f_0(x+t)\) prevents translation invariance, so no Fourier diagonalization has occurred. □

**Lean-ready head:** `domfm_canonical_two_frequency_kernel`, with the angular-frequency convention, Schwartz Fourier inversion and Fubini hypotheses proved from the displayed bounds, and conclusion (FOURIER).

### Lemma D2.4 — every positive diagonal absolute-Schur weight fails [ABSTRACT][PAPER]

Fix \(0<\epsilon<\log(7/5)\). A sufficient absolute-Schur certificate for \(T_\epsilon\ge0\) would be a positive finite measurable weight \(q(x)>0\) with
\[
 d_\epsilon(x)\ge\int |J_\epsilon|(x,dy)\frac{q(y)}{q(x)}
             \quad\text{for almost every }x.                    \tag{SCHUR}
\]
**No such q exists.** In particular the canonical choice \(q=1\) in ratio coordinates, corresponding to weight \(f_0\) in the original coordinates, fails.

**Proof of sufficiency, to identify the tested mechanism.** For any edge,
\[
 2|s(x)||s(y)|\le |s(x)|^2q(y)/q(x)+|s(y)|^2q(x)/q(y).
\]
Integrate against the symmetric positive measure \(dx\,|J_\epsilon|(x,dy)\). Condition (SCHUR) then bounds the off-diagonal pairing by the diagonal and proves a nonnegative form. This is only a sufficient test.

**Proof of impossibility.** Let
\(N_{-,\epsilon}:=\int_\epsilon^\infty b_-(t)C_0(t)dt\).
The negative part is away from zero, and the canonical correlation makes it finite. The cutoff retains the entire displayed negative interval, and
\[
 \int d_\epsilon(x)dx-\int a_\epsilon(x)dx=-4N_{-,\epsilon}.
                                                               \tag{DEFECT}
\]
For any positive q, symmetry and \(z+z^{-1}\ge2\) give, with Tonelli,
\[
 \begin{split}
 \iint\frac{q(y)}{q(x)}|J_\epsilon|(x,dy)dx
 &=\frac12\iint\left(\frac{q(y)}{q(x)}+
                     \frac{q(x)}{q(y)}\right)|J_\epsilon|(x,dy)dx\\
 &\ge\int a_\epsilon(x)dx.
 \end{split}
\]
If this integral is infinite, (SCHUR) already contradicts integrability of \(d_\epsilon\). If finite, integration of (SCHUR) contradicts (DEFECT) once \(N_{-,\epsilon}>0\).

Here is an explicit strict bound, without a numerical canonical value. On
\(I=[\log(7/5),\log(8/5)]\),
\[
 b(t)=\sqrt u\left((u^3-u)^{-1}-1\right)\le-43/168,
 \quad u=e^t,
\]
there are no prime-power atoms, and \(|I|=\log(8/7)\). For \(0\le z\le2\), the first positive term of (OBJECTS) gives
\[
 f_0(z)\ge\ell_0:=\frac{4\pi^2-6\pi}{A}e^{-\pi e^4}>0.
\]
For \(t\in I\) integrate \(C_0(t)\) over \(0\le x\le1\); both arguments lie in \([0,2]\), so \(C_0(t)\ge\ell_0^2\). Consequently
\[
 \boxed{\int(d_\epsilon-a_\epsilon)dx
 \le-\frac{43}{42}\ell_0^2\log(8/7)<0.}          \tag{SCHUR-KILL}
\]
This proves impossibility for the entire class of positive diagonal weights, not just for a chosen weight. □

The first invalid inequality in the proposed Schur proof is exactly (SCHUR). For \(q=1\) the failure is pointwise:
\[
 d_\epsilon(x)-a_\epsilon(x)
 =-2f_0(x)\int_\epsilon^\infty b_-(t)[f_0(x+t)+f_0(x-t)]dt<0.
\]
This is not a claim that the original (DOM) fails. It excludes the **absolute-value, unmodified-diagonal Schur certificate class**, including weights depending on epsilon. Block estimates that retain signs, error-tolerant schemes with independently justified budgets, and different exact representations are not excluded.

**Mandatory nonnegativity plant.** On three vertices,
\[
 2|s_1-s_2|^2+2|s_2-s_3|^2-|s_1-s_3|^2
       =|s_1-2s_2+s_3|^2\ge0.                     \tag{SIGNED-PSD}
\]
Its matrix is
\(\begin{pmatrix}1&-2&1\\-2&4&-2\\1&-2&1\end{pmatrix}\), has row sums zero and a negative interaction edge. The same absolute-Schur obstruction applies, while its form is positive semidefinite. Expansion proves the identity for all complex vectors. Therefore interpreting (SCHUR-KILL) as negativity of Q would be a demonstrable logic error.

**Lean-ready heads:** `domfm_signed_degree_defect` for (DEFECT); `domfm_no_positive_absolute_schur_weight` for a symmetric signed edge kernel with finite total variation and strictly negative integrated degree defect; `domfm_canonical_schur_defect_upper_bound` for (SCHUR-KILL); `domfm_signed_three_vertex_psd_plant` for (SIGNED-PSD). The finite version uses positive real weights, symmetric nonnegative absolute entries, finite sums and \(z+1/z\ge2\); it needs no zeta theory or spectral-gap estimate.

## D3. A concrete recovering family and the exact finite object

### Lemma D3.1 — actual CCM modes recover fixed tests in X [COFINAL_FAMILY][PAPER]

Choose the unchanged diagonal \(m=N\to\infty\), \(L=\log m\), and
\[
 \phi_{m,n}(x)=L^{-1/2}e^{2\pi in(x+L/2)/L}
                      \mathbf1_{[-L/2,L/2]}(x),\quad |n|\le m.
\]
Let \(\mathcal H_m\) be their full complex span and \(P_m\) the L² projection onto it. For each fixed compact smooth g,
\[
 \boxed{\|P_mg-g\|_X\longrightarrow0.}             \tag{REC-FORM}
\]

**Proof with a budget.** Eventually g is supported strictly inside the window. Four integrations by parts in its Fourier coefficients give, for the interior error h and its derivative,
\[
 \|h\|_\infty,\ \|h'\|_\infty
 \le \varepsilon_m(g):=\|g^{(4)}\|_1(L/m)^2.
\]
Both endpoint jumps are included in \(\operatorname{TV}(h)\le(L+2)\varepsilon_m\). Thus
\(D_h(t)\le\min(2(L+2)\varepsilon_m^2t,4L\varepsilon_m^2)\).
Integrating against a gives \(\mathcal D(h)\le14(L+2)\varepsilon_m^2\), and the weighted norm is at most \(mL\varepsilon_m^2\). Hence
\[
 \|P_mg-g\|_X\le\sqrt{mL+14(L+2)}\,\varepsilon_m(g)\to0.
                                                               \tag{REC-BOUND}
\]
No H¹ assertion about the zero-extended Fourier sum was used. This is the fixed-test proof, not a uniform estimate over moving unit vectors. For the noncompact \(f_0\), use the separate cutoff-and-tail budget [X, (REC-BUDGET)], not (REC-BOUND) with an unsupported compactness hypothesis. □

**Lean-ready head:** `domfm_literal_diagonal_fixed_test_X_recovery`, with the exact modes, `m → ∞`, `N=m`, fixed compact smooth g, and bound (REC-BOUND). The finite carrier is `CCMModeFinite m = Fin (2*m+1)` with integer label `i-m`.

### Lemma D3.2 — compressed GAP-GRAM, not automatic full positivity [FINITE_CELL][PAPER]

Let \(K_m=\operatorname{ccmWeilMatFinite}(m,m)\), complexified without changing its real entries. With the above orthonormal modes, define
\[
 G_t(i,j)=\langle\tau_t\phi_i-\phi_i,\tau_t\phi_j-\phi_j\rangle,
 \quad \alpha_i=\int\overline{\phi_i(x)}\cosh(x/2)dx,
 \quad \beta_i=\int\overline{\phi_i(x)}\sinh(x/2)dx,
\]
\[
 \begin{split}
 \Gamma_m&=\int_0^L a(t)G_tdt+\sum_{2\le n\le m}w_nG_{\log n}
                                      +2\alpha\alpha^*,\\
 c_L&=c_A+2\sum_{2\le n\le m}w_n-2\int_L^\infty a(t)dt.
 \end{split}
\]
Then the literal source identity is
\[
 K_m=\Gamma_m-c_LI-2\beta\beta^*.                 \tag{GRAM}
\]
For any synthesis matrix Z with range in the full mode carrier, put
\(H_Z=Z^*K_mZ\), \(G_Z=Z^*Z\). For every real e,
\[
 \boxed{H_Z+eG_Z\succeq0
 \iff Z^*\Gamma_mZ-(c_L-e)G_Z
                -2(Z^*\beta)(Z^*\beta)^*\succeq0.}              \tag{COMP-GAP}
\]
This assertion includes redundant Z, though a generalized eigenvalue notation requires the quotient by \(\ker Z\).

**Proof.** For \(g=\sum c_i\phi_i\), orthonormality gives \(\|g\|^2=c^*c\), \(D_g(t)=c^*G_tc\), and the pole term is \(2|\alpha^*c|^2-2|\beta^*c|^2\). Rewrite every prime term as
\(-2w_nC_g(\log n)=w_nD_g(\log n)-2w_n\|g\|^2\).
For \(t\ge L\), the two supports are disjoint up to null sets, giving \(D_g(t)=2\|g\|^2\). Substitution in the full form (Q) proves (GRAM) by polarization. The source crosswalk is the basis (2.6) and §4 of [C], with the literal constructors inspected in [F]: \(G_t(i,j)=2\delta_{ij}-q(U_i,U_j)(t)\), including the endpoint convention. The prime entries are precisely the finite weighted sum of that q. Direct integration gives \(\alpha_n=4L^{3/2}\sinh(L/4)/(L^2+16\pi^2n^2)\) and \(\beta_n=16i\pi n\sqrt L\sinh(L/4)/(L^2+16\pi^2n^2)\); their outer-product difference is `ccmW02Entry`. In the archimedean entry the tail beyond L contributes \(q(0)\log\tanh(L/2)/2\), exactly the logarithm in `ccmWREntry`. Thus this calculation concerns the literal matrix, not a new surrogate. It is a PAPER analytic calculation, not a new Lean analytic theorem. Congruence by Z gives (COMP-GAP) exactly. □

If Z has full row rank, (COMP-GAP) is equivalent to \(K_m+eI\succeq0\): every full coefficient vector is \(Zc\). If not, it is only the inequality on \(\operatorname{range}Z\). The plant \(K=\operatorname{diag}(-1,1)\), \(Z=(0,1)^T\), yields a positive compressed form and a negative full form. Thus a dictionary is not just a harmless change of basis unless its range is proved full.

The finite object controlling the best nonnegative error is
\[
 e_m^{\rm opt}=\max(0,-\lambda_{\min}(H_{Z_m},G_{Z_m})).
\]
This defines an error; it **does not prove its convergence to zero**. Proving such convergence still requires a lower bound in (COMP-GAP), not \(\Gamma_m\succeq0\) alone. [G] explicitly makes this distinction. The finite arithmetic in [M] does not bound the remaining signed interaction either.

**Lean-ready heads:** `domfm_compressed_gram_minus_shift`, with finite matrices and conclusion (COMP-GAP); `domfm_full_range_compression_posSemidef_iff`, with surjective synthesis; `domfm_proper_compression_negative_complement_plant`. The finite algebra can reuse `weilShiftMatrix_quadForm` and `weilShiftMatrix_posSemidef_iff`; the integral/source identification remains a separate PAPER obligation.

### Lemma D3.3 — cofinal zero-margin equivalence [COFINAL_FAMILY][PAPER]

Let \(V_m\subseteq\mathcal H_m\) be a predetermined family with this actual recovery property:
\[
 \forall g\in C_c^\infty(\mathbb R;\mathbb C)\quad
 \exists v_m\in V_m:\ \|v_m-g\|_X\to0.            \tag{DENS}
\]
The following are equivalent:

(i) Q is nonnegative on all complex compact smooth tests.

(ii) There exist \(e_m\ge0\), \(e_m\to0\), such that for every sufficiently large m and every \(v\in V_m\), \(Q(v)\ge-e_m\|v\|_2^2\).

The full choice \(V_m=\mathcal H_m\) satisfies (DENS) by D3.1. A proposed Fejér×heat dictionary must prove its own (DENS); [H]'s uniform density of a pointwise-positive cone is not that theorem.

**Proof.** Given (ii), choose the approximants from (DENS). Continuity (RAD-CONT) gives \(Q(v_m)\to Q(g)\), and their L² norms are bounded. Passing to the limit gives \(Q(g)\ge0\). Conversely, compact smooth density in X and continuity extend (i) to all X. Thus every \(V_m\subset X\) is nonnegative; choose \(e_m=0\). This is a logical equivalence, not the use of (i) as a premise in a purported unconditional proof of (i). □

At this **cofinal, recovering-family** level the dictionary and full GAP-GRAM reach the same remaining sign problem. At one finite cell a proper compression is strictly weaker. What a dictionary can change is conditioning, dimension, approximation cost and certificate cost. It has supplied no new lower bound merely by changing the coordinate functions.

[D] uses 40,001-point Riemann sums for coefficients, replaces Arb matrix entries by float midpoints, and performs NumPy Gram/Cholesky and eigenvalue calculations. Its own docstring limits meaningful margins to approximately \(10^{-12}\). Its \(-2\cdot10^{-15}\)-scale outputs therefore cannot certify zero-margin positivity. No run or independent interval verification of those 90 configurations was performed here.

**Lean-ready head:** `domfm_weil_nonneg_iff_recovering_compressed_lower_errors`, with X-continuity, exact synthesis membership, (DENS), and the fully quantified errors in (ii). It is an equivalence theorem, not a new positivity supplier.

## D4. Assembly, exact remaining inequality, and certificate boundary

### First remaining source inequality [COFINAL_FAMILY][CONDITIONAL]

One concrete, sufficient matrix target, with no family ambiguity, is
\[
 \boxed{\begin{gathered}
 \exists(e_m)_{m\ge2},\quad e_m\ge0,\quad e_m\to0,\\
 \forall m\text{ sufficiently large},\ \forall c\in\mathbb C^{2m+1}:\\
 c^*\Gamma_mc\ge(c_L-e_m)\|c\|_2^2+2|\beta^*c|^2.
 \end{gathered}}                                                \tag{ZG}
\]
The objects in (ZG) are exactly D3.2's integrals, prime powers and literal full modes. This is **not proved**. (GRAM), (REC-FORM) and D3.3 prove that an independent proof of (ZG) would yield W. Conversely W would imply (ZG) with zero errors. No fixed positive lower margin is needed.

The corresponding exact ratio target is
\[
 \boxed{\sum_{n\ge2}w_nE_s(\log n)
       +\int_0^\infty b_+(t)E_s(t)dt
       \ge\int_0^\infty b_-(t)E_s(t)dt
       \quad\forall s\in C_c^\infty(\mathbb R;\mathbb C).}       \tag{DOM}
\]
It is equivalent to W because \(g=f_0s\) and \(s=g/f_0\) both preserve compact smoothness, and D2.1 proves the exact form identity. This equivalence does not license arbitrary nonnegative t-functions in place of \(E_s\). D2.4 disproves a proposed sufficient proof method, not (DOM).

### Endpoint-complete finite-prime version [COFINAL_FAMILY][PAPER]

Here are the explicit finite objects and error budgets for the other representation. Use [X]'s dense class \(\mathscr E_1\): for every derivative order j there exists a function-dependent finite \(A_j(g)\) with
\(|g^{(j)}(x)|\le A_j(g)e^{-e^{2|x|}}\).
Let \(v\in\mathscr E_1\cap f_0^{\perp_X}\), \(\|v\|_2=1\),
\[
 C_v(t)=\Re\int\overline{v(x)}v(x+t)dx,\quad
 \Delta(t)=\sum_{2\le n\le e^t}\Lambda(n)-(e^t-1),\quad d_A=c_A-4,
\]
\[
 \begin{split}
 J_P(v)&=\int_0^{\log P}k(t)\|\tau_tv-v\|_2^2dt,\\
 S_P(v)&=2\int_0^{\log P}e^{t/2}C_v(t)dt
 -2\sum_{2\le n\le P}w_nC_v(\log n)
 +2\Delta(\log P)P^{-1/2}C_v(\log P),\\
 \mathcal A_P(v)&=J_P(v)+S_P(v)-d_A.
 \end{split}
\]
Put \(M_v=(\sqrt\pi/2)(A_0A_1+A_0^2/2)\). Then
\[
 E_S(v,P)=M_v\frac{1+\log P}{P}e^{-2P},\qquad
 E_J(v,P)=\frac8{5(1-P^{-2})}P^{-5/2},
\]
\[
 \boxed{\mathcal A_P-E_S\le Q(v)
                \le\mathcal A_P+E_S+E_J.}                      \tag{ENC}
\]
For each \(\eta>0\), take an integer
\[
 P\ge P(v,\eta):=\left\lceil\max\left\{2,
        (64/(15\eta))^{2/5},\ \tfrac12\log(1+2M_v/\eta)\right\}\right\rceil.
\]
Both errors are at most \(\eta/2\). The first remaining finite-prime assertion is
\[
 \boxed{\forall v\in\mathscr E_1\cap f_0^{\perp_X},\ \|v\|_2=1,
 \quad\forall\eta>0,\quad\exists P\ge P(v,\eta):
              \mathcal A_P(v)\ge-\eta.}                       \tag{FM}
\]
It too is **not proved**.

**Proof of the budgets and conditional assembly.** The envelope gives
\(|C_v'(t)-C_v(t)/2|\le M_ve^{-t/2}e^{-2e^t}\): bound the product envelope using
\(e^{2|x|}+e^{2|x+t|}\ge2e^t\cosh(2x+t)\) and integrate the resulting Gaussian majorant. Stieltjes integration by parts on \([0,\log P]\) gives exactly \(S_P\), with the positive endpoint term and the atom at P included. The elementary bound \(|\Delta(t)|\le e^t(1+t)\) gives
\[
 |\mathcal S-S_P|\le2M_v\int_P^\infty(1+\log x)x^{-1}e^{-2x}dx\le E_S.
\]
The omitted J tail is nonnegative and at most \(E_J\), since \(\|\tau_tv-v\|^2\le4\). This proves (ENC) with the correct asymmetric error sides. The cutoff follows from \((1+\log P)/P\le1\) and \((1-P^{-2})^{-1}\le4/3\).

If (FM) is independently proved, (ENC) gives \(Q(v)\ge-3\eta/2\) for every eta, hence \(Q(v)\ge0\). For any compact smooth g set
\(\Pi g=g-\langle f_0,g\rangle_X f_0/\|f_0\|_X^2\).
It belongs to the indicated dense smooth class, is X-orthogonal to \(f_0\), and has \(Q(\Pi g)=Q(g)\) by the radical identity. Normalization, with the zero vector handled separately, yields W. Conversely W extends to X and (ENC) gives \(\mathcal A_P\ge-E_S-E_J\ge-\eta\) at the displayed cutoff. Thus this FM really has the same zero-margin target. Only after W has been established does the published Weil criterion [W] yield RH. Its premise has not been discharged here. □

**Lean-ready heads:** `domfm_endpoint_complete_prime_enclosure` for (ENC); `domfm_zero_margin_prime_family_iff_weil_nonnegative` for the last equivalence; `domfm_zero_margin_literal_matrix_family_implies_weil_nonnegative` for the implication from (ZG). Proposed analytic heads name their exact definitions above. They do not introduce project axioms or claim that the explicit formula is already formalized in Mathlib.

### What a certificate must enclose

For one test, a **lower envelope** \(L(\mathcal A_P)-U(E_S)\ge0\) proves its nonnegativity. An **upper envelope** \(U(\mathcal A_P)+U(E_S)+U(E_J)<0\) is a negative-test certificate. An interval containing zero is inconclusive for exact positivity.

For zero-margin exhaustion, a certified lower bound \(-e_m\) is useful even when it is negative, provided a separate theorem proves \(e_m\to0\). Label it `LOWER_BOUND_CERTIFIED`, not a positivity PASS. For a finite dictionary certify \(H_Z+e_mG_Z\succeq0\) on all coefficient vectors with the actual Gram matrix, exact range and common source. Entrywise nonnegative intervals or selected Rayleigh samples are insufficient. A negative direction requires a nonzero coefficient vector and a strict certified upper bound on its actual quadratic value.

The canonical identity is handled symbolically, not by waiting for floating-point zero. A finite Xi row is not licensed for exact nullspace deflation. It requires either an exact null identity or a proved residual-and-coupling budget.

**DISCRIMINATOR:** `SIGNED_ZERO_MARGIN_ENCLOSURE_WITH_SAME_FAMILY_RECOVERY`: the two one-sided bounds in (ENC), or an exact finite-matrix lower bound plus the full cofinal error proof and (DENS). Kernel degree defects and failure of sufficient tests are not substitutes for this discriminator.

## Prediction ledger and independent-check registrations

Observer probabilities are unchanged. Fates concern this batch, not future mathematical possibility.

| Prediction | p | Fate |
|---|---:|---|
| `P_D1_TRADEOFF_PROVED_AND_TYPED_LEAN_READY` | 0.90 | CONFIRMED WITH GUARDS: stronger (TRADE), nonzero projection, genuine operator norm, form-density repair. Not kernel-verified. |
| `P_D2_EXPLICIT_KERNEL_T_WRITTEN` | 0.70 | CONFIRMED: explicit cutoff kernel, degree, uncut difference form and Fourier kernel. The requested raw finite diagonal needed correction. |
| `P_D2_POSITIVITY_TEST_IDENTIFIED` | 0.30 | CONFIRMED: (SCHUR) is a precise sufficient test; its entire positive-weight class fails by (SCHUR-KILL). |
| `P_D3_ZERO_MARGIN_REDUCES_TO_GAP_GRAM` | 0.80 | CONFIRMED AT THE RECOVERING-FAMILY LEVEL; finite proper compression is weaker, not equivalent to the full-cell inequality. |
| `P_RESULT_COMPLETE` | 0.02 | REFUTED as this batch's outcome. |
| `P_RESULT_PARTIAL` | 0.88 | CONFIRMED. |
| `P_RESULT_REFUTED` | 0.10 | REFUTED as the overall result; scoped theorem-shape refutations occur inside the partial result. |

Before the Schur-class proof was checked in this turn, the adjudicator registered in the conversation the prediction that positive reweighting would not rescue this absolute-value test, p=0.85. Its fate is **CONFIRMED by D2.4**, not by a numerical test. The earlier sharpening of D1 was not advertised as a blind prediction.

[A] reports SURVIVES for the four unchanged XIDEV probabilities 0.88, 0.84, 0.78, 0.88. This document records that external PAPER audit and preserves its caveat that the literal finite carrier crosswalk was not independently checked by that audit. It does not rescore the old numerical predictions. The exact \(d_A=\gamma+\log(8\pi)+\pi/2-4\) is used; [A] identifies the old request's decimal constant as the error. No new decimal certification is claimed.

Register now, before future independent checks:
```yaml
P_DOMFM_SHARP_TRADEOFF_AND_FORM_TOPOLOGY_SURVIVE:
  probability: 0.94
  event: independent_review_preserves_TRADE_and_FORM_TRADE_with_the_stated_guards
  fate: PENDING
P_DOMFM_KERNEL_FACTORS_AND_UV_BUDGET_SURVIVE:
  probability: 0.87
  event: independent_review_preserves_PAIR_FOURIER_UV_BUDGET_and_log_diagonal
  fate: PENDING
P_DOMFM_ALL_POSITIVE_SCHUR_WEIGHT_OBSTRUCTION_SURVIVES:
  probability: 0.91
  event: independent_review_preserves_SCHUR_KILL_without_a_positivity_premise
  fate: PENDING
P_DOMFM_COMPRESSED_RECOVERY_SCOPE_SURVIVES:
  probability: 0.89
  event: independent_review_preserves_finite_range_caveat_and_cofinal_equivalence
  fate: PENDING
```

## Route map, dependency epistemics and closeout

**R1 — coupled signed-energy certificates.** Retain negative continuous interactions and pay for them using identities between realizable differences, as (SIGNED-PSD) does, rather than entrywise absolute values. Target exactly (DOM). Main risk: replacing constrained differences by arbitrary nonnegative functions or losing the canonical weights. Estimated kill-power/cost: **9/10 / 7/10**. These are qualitative proof-effort scores, not measured runtimes.

**R2 — full CCM Gram-minus-shift lower certificates.** Work on the existing diagonal, or an exactly recovering compression, and certify (ZG)/(COMP-GAP) with vanishing negative errors. Main risk: dropping a near-null direction, changing the Gram norm, or leaving the recovery theorem unproved. Estimated kill-power/cost: **9/10 / 7/10**. No new experiment is authorized.

**Selected direction:** R1 with genuinely coupled signed blocks; R2 supplies the independent same-object sign discriminator. Absolute scalar Schur reweighting is retired, not replaced by a spectral-gap operator-norm bound. An exact negative-edge square identity can succeed where scalar absolute dominance cannot; (SIGNED-PSD) proves this distinction, not its arithmetic instantiation.

**Strongest attack.** This remains a reformulation and exclusion result, not the missing lower bound. Correct: no canonical RH supplier was closed. The additional proved content is the quantitative quadratic margin obstruction, the explicit singular kernel/Fourier kernel, the all-positive-weight Schur impossibility, and the finite-range versus recovering-family distinction. None establishes the sign of (DOM).

```yaml
K8A:
  DOWNSTREAM_CONSUMER: published_Weil_criterion_on_all_complex_compact_smooth_tests
  ACTUAL_CONSUMER_REQUIREMENT: Q_g_nonnegative_for_every_such_g
  ORIGINAL_REQUESTED_OBJECT: DOM_or_FM_at_zero_margin
  ORIGINAL_OBJECT_IS: PROVED_NECESSARY
  EQUIVALENCE_SCOPE: exact_canonical_form_and_stated_recovering_class_only
  KNOWN_WEAKER_INTERFACES:
    - ZG_vanishing_full_matrix_lower_errors_plus_REC_FORM_implies_W
    - test_dependent_FM_tolerances_and_exact_tail_budgets_imply_W
    - direct_DOM_on_compact_smooth_ratios_implies_W_by_positive_f0_division
  OPTIONAL_FAILED_OBJECT: positive_diagonal_absolute_Schur_certificate
  OPTIONAL_FAILED_OBJECT_IS: NOT_NECESSARY
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  MINIMAL_MISSING_IDENTITY: DOM_or_equivalently_the_quantified_zero_margin_lower_supply_ZG_FM
  NOVELTY_AXIS: exclude_all_scalar_absolute_reweightings_while_retaining_signed_block_cancellations
  REOPEN_TRIGGER: source_specific_coupled_lower_bound_with_no_free_positivity_premise
  ROUTE_FAMILY_DEATH: false
SCOPED_KILL_DEPENDENCIES:
  uniform_positive_margin:
    necessary_for_consumer: false
    exact_scope: same_Q_same_L2_norm_family_approximating_f0_in_X
    evidence: MARGIN_KILL
    excluded_inferences: fixed_window_strict_positivity_and_bare_L2_density
  absolute_Schur:
    necessary_for_consumer: false
    exact_scope: cutoff_kernel_unmodified_signed_degree_and_any_positive_diagonal_weight
    evidence: SCHUR_KILL
    excluded_inferences: nonpositivity_of_Q_or_failure_of_signed_block_certificates
```

**One local directive, not execution authorization:** independently check and formalize the finite signed-degree obstruction underlying `domfm_no_positive_absolute_schur_weight`, then audit its single continuum instantiation (KERNEL)–(SCHUR-KILL). The unchanged consumer requirement is the actual zero-margin domination, not positivity of the representing measure. Required inputs are a symmetric signed edge matrix/measure, finite total variation and the proved negative degree defect. Use pairwise symmetrization and \(z+1/z\ge2\). The success gate must accept the impossibility conclusion while retaining the positive-semidefinite plant (SIGNED-PSD). Report any normalization/domain defect as `DOMFM_SCHUR_OBSTRUCTION_SOURCE_MISMATCH`. No Lean edit, numerical run or submission is authorized in this transaction.

```yaml
META_CLOSEOUT:
  PROGRESS_CLASS: FALSIFICATION_PROGRESS
  COGNITIVE_OPERATOR: COUNTEREXAMPLE_HUNT
  ROUTE_SCORE: 4
  WHAT_BECAME_SMALLER: scalar_absolute_Schur_certificate_class_excluded_completely
  WHAT_WAS_KILLED: uniform_form_dense_positive_margin_and_all_positive_absolute_Schur_reweightings
  FORBIDDEN_REPEAT: infer_negativity_of_the_form_from_failure_of_a_sufficient_certificate
  CURRENT_SMALLEST_GAP: source_specific_coupled_zero_margin_domination_DOM_ZG_FM
  NEXT_DECISIVE_TEST: independent_check_of_the_signed_degree_obstruction_and_its_source_instantiation
  iteration:
    target: DOM_FM_zero_margin
    status: PROGRESS
    failed_strategy: scalar_absolute_diagonal_dominance_around_the_canonical_radical
    invariant_learned: zero_row_sum_and_negative_edges_defeat_every_positive_absolute_reweighting_not_every_PSD_proof
    forbidden_future_move: absolute_value_each_edge_then_tune_a_positive_weight
```

## Verification handoff

Write only `EXPECTED_VERDICT_PATH` on `rh_clean` under a `[Proshka]` commit subject. Old verdicts, request bytes, queue, phase key and shared state remain unchanged. The resulting commit and blob are returned in the post-write receipt rather than recursively inserted into their own file.

This is a documentation-only PAPER verdict. No Lean source exists from this transaction, so there is no new Lean blob, no executed `lake` gate and no kernel certification. Proposed heads require actual definitions and proofs; no `sorry`, project axiom or altered statement is supplied. The expected axiom profile of a future completed formalization is `[propext, Classical.choice, Quot.sound]`. A successful source write or independent check of D1–D3 leaves the overall result PARTIAL. Only an independently established (DOM), (ZG), or (FM), with the exact source imports and recovery, could change that mathematical result. It would not automatically authorize route promotion or a PX_RH_CLAIM.
