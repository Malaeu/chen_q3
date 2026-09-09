# STATUS: TRY_SCHUR_PAPER_CONSTRUCTION_WITH_PRECISE_REMAINDERS
```yaml
OPERATIVE_CLASS: TRY_SCHUR_PAPER_CONSTRUCTION_WITH_PRECISE_REMAINDERS
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-09-SCHUR
BOUNDARY_ID: GOAL058_RADICAL_TRIAL_SCHUR_T_SQUARED_SUPPLIER
RESULT:
  Q1: PARTIAL_WITH_PRECISE_REMAINDER
  Q2: PARTIAL_WITH_PRECISE_REMAINDER
  Q3: PARTIAL_WITH_PRECISE_REMAINDER
  OVERALL: PARTIAL_WITH_PRECISE_REMAINDER
REQUEST_LOCK:
  REPOSITORY: Malaeu/chen_q3
  BRANCH: rh_clean
  COMMIT: e11338a3a9132c88895b565d74ce189503d1c642
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_SCHUR_2026-09-09.txt
  GIT_BLOB: 2b3dab1d1eb6cda458bb0d12a96cf8209660f271
  SHA256: 4c082be285b9d38df78d8e9ef50771798db1469492ed0ab22602ab7520ab418f
  BYTES: 13296
  LINES: 89
  FINAL_LF: true
  ATTACHMENT_HASHES_RECOMPUTED: true
  CONNECTOR_READ_AT_EXACT_COMMIT: true
  ATTACHMENT_GIT_BLOB_MATCHES_CONNECTOR: true
SOURCE_BASE: e4fa8439f2dd98b3b7192cbb4dbe06d102425be8
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
DERIVATIONS:
  GLOBAL_RADICAL_AND_FINITE_CUT_DOMAIN: PAPER_PROOF_GIVEN
  EXACT_PHYSICAL_GRAM_RANK: PAPER_PROOF_GIVEN
  SOURCE_DEFINED_FINITE_COEFFICIENT_CONSTRUCTION: PAPER_PROOF_GIVEN
  UNCONDITIONAL_WEAKER_UPPER_RATE: C_exp_2a_times_T_over_one_minus_T
  COFINAL_DEGREE_LAW: NOT_PROVED
  POSITIVE_TAIL_REFERENCE_MATRIX_INVERTIBLE: PAPER_PROOF_GIVEN
  SIGNED_Q_MATRIX_AUTOMATICALLY_POSITIVE: false
  ONE_DIRECTION_TAIL_DETERMINANT: PAPER_PROOF_GIVEN
  MULTIDIRECTION_TAIL_SCHUR_IDENTITY: PAPER_PROOF_GIVEN
  NONPOSITIVE_DIRECTION_IMPLIES_STRONG_AFFINE_BUDGET: false
  AUTOCORRELATION_ABSOLUTE_CONTINUITY: PAPER_PROOF_GIVEN
  COUPLED_ARITHMETIC_IDENTITY: PAPER_PROOF_GIVEN
  T_SQUARED_UNNORMALIZED_BUDGET_PAID: false
  T_SQUARED_NORMALIZED_BUDGET_PAID: false
  LOWER_SIGN_SUPPLIER: NOT_PRODUCED
FIRST_FAILURE:
  Q1: uniform_growth_of_the_explicit_tail_Gram_inverse_functional
  Q2: signed_tail_Schur_remainder_at_epsilon_times_N_squared
  Q3: signed_D_psi_autocorrelation_integral_together_with_the_full_main_term
PREDICTION_FATES:
  P_DEGREE_UNPAID: {probability: 0.70, fate: CONFIRMED}
  P_DETERMINANT_INTERFACE: {probability: 0.90, fate: CONFIRMED}
  P_ARITHMETIC_REMAINDER: {probability: 0.80, fate: CONFIRMED}
  P_UPPER_NOT_SIGN: {probability: 0.99, fate: CONFIRMED}
  NUMERICAL_FORECAST_A075_K48_M6:
    frozen_value: 1.5
    fate: UNRESOLVED
    reason: no admissible total-error-resolved result supplied or run here
EVIDENCE:
  SCOPES: [ABSTRACT, FINITE_CELL, COFINAL_FAMILY]
  VERIFIER: PAPER
  INDEPENDENT_PAPER_VALIDATION: PENDING
  LEAN_VERIFIED: false
  SHELF_SHA256_PREFIX_VERIFICATION_COMPLETE: false
  SHELF_HASH_LIMITATION: see_section_0
EXECUTION:
  NEW_NUMERICAL_RUN: false
  SOURCE_SCRIPTS_EXECUTED: false
  LEAN_EDIT: false
  LEAN_GATE: NOT_RUN
  QUEUE_OR_STATE_EDIT: false
  EXECUTION_GRANT: NONE
PUBLICATION:
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SCHUR_2026-09-09.md
  LOCAL_ARTIFACT_CREATED: true
  REPOSITORY_COMMIT: NOT_CREATED
  PUSH: NOT_PERFORMED
  BLOCKER: current_GitHub_connector_exposes_no_write_or_push_action_and_CLI_cannot_resolve_github_com
  EXISTING_VERDICT_PATH_CHECK: NOT_FOUND_AT_CHECK
  HISTORICAL_ARTIFACTS_MODIFIED: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## 0. Decision, source locks, and delivery limitation

**The full tail-determinant interface survives. A cofinal degree schedule and its T-squared estimate do not follow from the present calculations.** This verdict supplies an explicit finite coefficient construction, proves its admissibility and rank, derives a positive-reference tail bound without assuming the sign of Q, handles the singular Schur branches, and writes the remaining signed arithmetic integral for that actual trial. It does not label those reductions a proof of the requested rate. [ABSTRACT][PAPER; COFINAL_FAMILY][CONDITIONAL for the rate]

There is one exact correction to the strong target: a nonzero direction of zero Q-energy can establish the normalized upper bound while failing to supply the stronger affine inequality for J. Section 3.4 gives a radical-compatible counterexample. This does not refute the actual-source upper-rate law. [ABSTRACT][PAPER]

**Integrity disclosure.** The attached request was read in full, fetched at its exact GitHub commit, and its bytes, line count, SHA-256 and Git blob were independently recomputed and matched. All ten shelf paths were fetched at SOURCE_BASE during this continued audit. The earlier interrupted work successfully recomputed the full SHA-256 for BATCH_PATTERNS and one_direction_margin.py. I did not complete independent SHA-256 recomputation for the other eight shelf files. Their declared SHA-256 values below are binding metadata, not a claim that I recalculated them. No hash mismatch was observed. The requested complete shelf-prefix check is therefore **not claimed complete**. Source readings and newly derived mathematics are distinguished from that remaining integrity check.

**Delivery disclosure.** The current GitHub tool discovery returned no create/update/commit/push action. Plugin discovery found the already-installed GitHub integration, not another usable write connection. The expected verdict path was absent when checked. A CLI read-only connectivity check also failed with `Could not resolve host: github.com` (exit 128). This file is the requested local verdict artifact, but it has **not been committed or pushed**. Prior conversations' write receipts do not establish a write operation in this session.

All paths in the following table are relative to the repository root and fixed at SOURCE_BASE. READ means content was inspected, not that its mathematical claims were accepted. RELAY remains a provenance classification even when the relay text was read. No historical diagnostic is promoted to interval certification.

| Key | Path | Declared SHA-256 | Git blob at pin | Reading / independent SHA check |
|---|---|---|---|---|
| B | `docs/BATCH_PATTERNS.md` | `cded6dfd5950fd8dd230ad770ff0cf4a50a5bea9b2d5e91601b8eaa76120903b` | `cb63bab5fbff3d39bf63c0b0f081a2264e004f2b` | READ; SHA recomputation matched in continued work |
| D | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_DISTANCE_2026-09-09.md` | `2ad89fd43395242af8de2ed61383dd481057ae079cbd109aa32443e25edf1c5c` | `11979ce43d5e974080afa6690bb81e07f67f745e` | READ relevant proofs D2-D24 and closeout; SHA not independently recomputed |
| I | `docs/routeB_bus/DISTANCE_INDEPENDENT_CHECK_2026-09-09.md` | `a54961ff784e6f1272a4b30cd4140ee320499101187bb7b95ea35c96b3d3f43d` | `168606c055b4839a0cbe1d51256cfae542e6d9e6` | READ derivation checks and diagnostics; SHA not independently recomputed |
| S | `docs/routeB_bus/proshka/PROSHKA_SUPPLEMENT_GOAL058_DISTANCE_SCHUR_POINT5_2026-09-09.md` | `3db1149291635de9dbca9148c778a8cef904ddac2e930a3b846b117a8bca4393` | `c7220e653535515aab013e63ea25f295cfc2a45c` | RELAY, text read; equations rederived below; SHA not independently recomputed |
| A | `docs/routeB_bus/proshka/PROSHKA_ADDENDUM_GOAL058_DISTANCE_SCHUR_2026-09-09.md` | `7027bf2b5323f183b2e8af298230d68685c423fb31e4585d571f002626e80f04` | `e456429ba1a55ca04d70d7c3e571979a14aa56aa` | READ diagnostic report; SHA not independently recomputed here |
| W | `docs/routeB_bus/WINDOW_TAIL_DERIVATIVE_PROBE_2026-09-09.md` | `3807727e0eb78dd7208003753f1c7e97a9f424b7c069a0c45d58dcee972ad123` | `420b11653591629b38fefaa2ba533c19a823154a` | READ, including final span table; SHA not independently recomputed |
| O | `docs/routeB_bus/phase5_codex/six_centre/one_direction_margin.py` | `667899c1bcf620be3c662daad8a1073d3964b16bc15564ed0e7331fc8e7756ca` | `608142948a8e6c7bff506b213c6b49268bd4c97d` | READ in full; SHA recomputation matched in continued work; NOT executed |
| V | `docs/routeB_bus/phase5_codex/six_centre/window_derivative.py` | `545b47b24175b6e04b458da1b06bb827f7c52f162a10437d1d866ef647a73f3c` | `ddce881cd1c51c46b397c26633fdba217aae2a26` | READ in full; SHA not independently recomputed; NOT executed |
| C | `docs/routeB_bus/phase5_codex/six_centre/sc_build.py` | `e52f96dff9c04d76963d285ce9055d21f95cc0a340b9c9b3bde67a5bed7db6dc` | `4b62261b2b17416854702e0bd0c178a87844fc20` | READ in full; SHA not independently recomputed; NOT executed |
| K | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_KERNEL_2026-09-08.md` | `e91899971d56423cea42cfb8ba0c1a1f8a8980b90ac3990f69273a1dfdf1cca5` | `d171a2fb7b6b917a1780656952b1db5458cc9a34` | READ K6-K26 and context; SHA not independently recomputed |

The meanings of the source and scalar are those of D2-D3, not a different theta normalization in K18. All prior paper proofs are PAPER_DERIVATION_TO_RECHECK. The proofs used here are rechecked below, with the signed explicit formula cross-checked against the primary source [S26, (3.1)].

## 1. Common foundation: exact form, radical, cut domain and rank

Every lemma in this section is [ABSTRACT][PAPER]. Instantiation at any fixed a and m is also [FINITE_CELL][PAPER]. None presumes positivity of Q.

### 1.1 Full source and continuity

Use the antilinear-first physical inner product and translations
\[
\langle f,g\rangle=\int_{\mathbb R}\overline{f(x)}g(x)\,dx,
\qquad U_tg(x)=g(x-t).
\]
Put
\[
A_0(t)=\frac{e^{-t/2}}{1-e^{-2t}},\quad
c_A=\gamma_E+\log(8\pi)+\frac\pi2,\quad
w_n=\frac{\Lambda(n)}{\sqrt n}.
\]
The form is exactly
\[
\begin{split}
Q(f,g)={}&\mathcal D(f,g)-c_A\langle f,g\rangle
-\sum_{n\ge2}w_n\{\langle f,U_{\log n}g\rangle+\langle f,U_{-\log n}g\rangle\}\\
&+\overline{M_+(f)}M_-(g)+\overline{M_-(f)}M_+(g),\\
\mathcal D(f,g)={}&\int_0^\infty A_0(t)\langle U_tf-f,U_tg-g\rangle\,dt,\\
M_\pm(f)={}&\int f(x)e^{\pm x/2}\,dx,\qquad
\|f\|_E^2=\mathcal W[f]+\mathcal D[f],\quad
\mathcal W[f]=\int e^{2|x|}|f(x)|^2dx. \tag{S1}
\end{split}
\]
Weighted Cauchy-Schwarz and |x|+|x-t|>=|t| give
\[
|\langle f,U_tg\rangle|\le e^{-|t|}\sqrt{\mathcal W[f]\mathcal W[g]},
\qquad |M_\pm(f)|\le\sqrt{4/3}\sqrt{\mathcal W[f]}.
\]
Since c_A<7 and sum_{n>=2} log(n)n^{-3/2}<6, another two-component Cauchy-Schwarz inequality gives
\[
|Q(f,g)|\le \sqrt{\mathcal D[f]\mathcal D[g]}
 +\frac{65}{3}\sqrt{\mathcal W[f]\mathcal W[g]}
\le22\|f\|_E\|g\|_E. \tag{S2}
\]
These constants need no prime-number theorem. For example the decreasing function log(x)x^{-3/2} is bounded by its first term plus its integral on [2,infinity).

For a check of normalization against [S26], its archimedean point constant is log(4pi)+gamma_E before rewriting as a translation-difference form. The additional constant is
\[
2\int_0^\infty A_0(t)(1-e^{-t/2})dt
=4\int_0^1\frac{du}{(1+u)(1+u^2)}=\log2+\pi/2.
\]
This gives precisely c_A. Swapping the arguments converts that paper's linear-first convention to ours. Its Fourier variable must also be converted to our Laplace variable; no sign or prime-power coefficient changes.

### 1.2 Theta normalization and global radical membership

For the requested Phi, direct Mellin integration with s=1/2+z, initially Re(s)>1, gives
\[
F_\Phi(z)=\pi^{-s/2}\zeta(s)
 [\Gamma(s/2+2)-\tfrac32\Gamma(s/2+1)]
=\tfrac14s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)
=\tfrac12\xi(s). \tag{S3}
\]
Here xi is the standard normalization [N, 25.4.4]. Theta inversion [NT, 20.7.32 at z=0, tau=iu, u>0] gives evenness. One can see the cancellation directly: if theta(u)=sum_{n in Z} exp(-pi n^2 u), then
Phi(x)=u^{9/4}theta''(u)+(3/2)u^{5/4}theta'(u), u=e^{2x}; differentiating theta(u)=u^{-1/2}theta(1/u) cancels the derivative-free term and gives Phi(-x)=Phi(x). The positive-side series and this identity show double-exponential decay of every fixed derivative at both ends. They justify continuation of (S3), all integrations by parts, and membership in E.

In particular M_+(Phi)=M_-(Phi)=1/4. The full E space, not the pole-null subspace, is essential.

For a compact smooth test h, the signed explicit formula in our convention is
\[
Q(v,h)=\sum_{\lambda}m_\lambda\,
\overline{F_v(-\overline\lambda)}F_h(\lambda), \tag{S4}
\]
where lambda ranges over distinct centered zeros. This is [S26, (3.1)] after the stated convention change. For v in E it follows from the compact-smooth case by (S2), bounded strip evaluation, rapid decay of F_h on vertical lines and the unconditional zero-count bound. Compact smooth functions are dense in E: cut off smoothly, estimate the translated product error by min(t/R,1), and then mollify in the logarithmic Fourier norm and the weighted L2 norm. Thus (S4) and (S2) extend radical identities to every second argument in E.

Integration by parts gives
\[
F_{g_k}(z)=(z^2-1/4)(-z)^kF_\Phi(z),\qquad
Q(\Phi,h)=Q(g_k,h)=0\quad(h\in E). \tag{S5}
\]
This is global radical membership, not merely Q[g_k]=0. Neither RH nor zero simplicity was used. Originally M_+(g_k)=M_-(g_k)=0; the orthogonalization below generally destroys this pole-null condition. Both pole terms remain in Q.

### 1.3 The cuts really belong to V_a

Let v be any finite linear combination of Phi and its derivatives. For either its inside or outside sharp cut, the distributional derivative is the ordinary piecewise derivative plus the two endpoint atoms. Minkowski followed by the three-term square inequality gives, for 0<t<1,
\[
\|U_t(1_{|x|>a}v)-1_{|x|>a}v\|_2^2
\le3t^2\|1_{|x|>a}v'\|_2^2
 +3t\bigl(|v(a)|^2+|v(-a)|^2\bigr). \tag{S6}
\]
The analogous inside estimate also holds. Since A_0(t)<=2/t on (0,1), these jumps have finite logarithmic energy. At infinity use the integrability of A_0 and translation invariance of L2.

For inward smooth tapers of the inside cut, the error has L2 mass O(delta), bounded amplitude and bounded variation for fixed a and v. Its translation difference is O(min(t,delta)), and hence its E-energy is O(delta(1+|log delta|)). This proves membership in the E-closure V_a of compact smooth functions supported strictly inside (-a,a). It covers both endpoints and both taper junctions. No global H1 requirement is imposed on the sharp cut. These constants are fixed-function constants; they are not claimed uniform in m.

### 1.4 Orthogonalize before cutting; exact linear independence

For a>0, define N=N_a>0 and
\[
\alpha_j=\frac1{N^2}\int_{-a}^a\Phi(x)g_{2j}(x)dx,
\quad h_j=g_{2j}-\alpha_j\Phi,
\quad d_j=1_{(-a,a)}h_j,
\quad e_j=1_{|x|>a}h_j. \tag{S7}
\]
The alpha_j are real source integrals. Each h_j is a GLOBAL radical vector, d_j belongs to V_a, and <p_a,d_j>=0. This gives exactly the directions in the request, not new directions.

For every finite m, d_0,...,d_m are linearly independent. Indeed, a linear combination vanishing almost everywhere on (-a,a) vanishes there pointwise by continuity. The underlying h-combination is real analytic and therefore vanishes on the entire real line. Taking its Laplace transform and using F_Phi not identically zero gives the polynomial identity
\[
(z^2-1/4)\sum_{j=0}^m c_jz^{2j}-\sum_{j=0}^m c_j\alpha_j=0.
\]
At z=1/2 the constant sum is zero; all remaining coefficients must then vanish. The same argument on either open outside interval proves independence of e_0,...,e_m. It also proves independence of Phi,g_0,...,g_{2m} on either the inside or outside interval.

Consequently
\[
\dim S_{m,a}=m+1,\qquad G_{ij}=\langle d_i,d_j\rangle\text{ is positive definite}. \tag{S8}
\]
This is **physical Gram positivity**, not positivity of C_{ij}=Q(d_i,d_j).

## 2. RESULT Q1 — PARTIAL_WITH_PRECISE_REMAINDER

**Exact requested claim.** There exist fixed M>0, nu>=0, a_*>0, an integer-valued m(a), and a deterministic source construction z_a in S_{m(a),a}, for all a>=a_*, such that Q[p_a-z_a]<=M exp(nu a)T(a)^2. This claim is not proved below. What is proved is a construction for every a>0 and every finite m, with an explicit upper bound and an explicit first coefficient inequality needed for the cofinal claim. [COFINAL_FAMILY][CONDITIONAL; FINITE_CELL][PAPER]

Inputs: [D, D2-D8,D15-D17], [K, K8-K18], [O] for the derivative recurrence and projection convention; all at SOURCE_BASE. The recurrence and new estimates are derived here, not assumed from the scripts.

### 2.1 A deterministic construction which never asks whether Q is positive

For an even smooth v in the finite radical span define the positive tail majorant
\[
\mathfrak B_a[v]=\int_{|x|>a}
 \left[(e^{2|x|}+16a+16)|v(x)|^2+3e^{-4a}|v'(x)|^2\right]dx
 +6e^{-2a}\left(|v(a)|^2+|v(-a)|^2\right). \tag{S9}
\]
Split the Dirichlet integral at delta=e^{-2a} and at 1. On (0,delta) use (S6); on (delta,1) use ||U_t w-w||_2^2<=4||w||_2^2; above 1 use A_0(t)<=2 exp(-t/2). This proves
\[
\|1_{|x|>a}v\|_E^2\le\mathfrak B_a[v],
\qquad |Q[1_{|x|>a}v]|\le22\mathfrak B_a[v]. \tag{S10}
\]
The large-t term is at most 16||1_out v||_2^2. The small-t terms are at most 3 delta^2||1_out v'||_2^2 and 6 delta times the two squared traces. The middle interval contributes at most 8 log(1/delta)||1_out v||_2^2=16a||1_out v||_2^2. Thus every constant and a-dependent weight in (S9) has a source-independent proof. This positive reference bound changes the coefficient construction only; it does not change Q, its physical norm, support or derivative family.

Let u_0=Phi and u_{j+1}=g_{2j}, 0<=j<=m. Polarize (S9) and set
\[
H_{ij}=\mathfrak B_a(u_i,u_j),\qquad
\ell=(1,\alpha_0,\ldots,\alpha_m)^T,\qquad
Z_{m,a}=\ell^*H^{-1}\ell. \tag{S11}
\]
H is strictly positive definite: a zero B-norm forces the corresponding analytic combination to vanish on an outside interval, and Section 1.4 forces all coefficients to vanish. Since ell is nonzero, Z_{m,a}>0.

Define, using source quantities only,
\[
\theta=\frac{H^{-1}\ell}{Z_{m,a}},\qquad
v_{m,a}=\sum_{i=0}^{m+1}\theta_i u_i,
\qquad f_{m,a}=\frac{1_{(-a,a)}v_{m,a}}N,
\qquad z_{m,a}=-\frac1N\sum_{j=0}^m\theta_{j+1}d_j. \tag{S12}
\]
These quantities are real and even. The identity ell*theta=1 gives
\[
f_{m,a}=p_a-z_{m,a},\quad
\langle p_a,f_{m,a}\rangle=1,\quad
\|f_{m,a}\|_2^2=1+\|z_{m,a}\|_2^2\ge1. \tag{S13}
\]
Furthermore, weighted Cauchy-Schwarz proves
\[
\min_{\ell^*\eta=1}\eta^*H\eta=\frac1{Z_{m,a}},
\qquad \mathfrak B_a[v_{m,a}]=\frac1{Z_{m,a}}.
\]
The minimizer formula follows either from equality in that Cauchy-Schwarz inequality or by completing the H-square. Since v_{m,a} is global radical, its two cuts have equal Q-energy. We have therefore proved the unconditional finite construction bound
\[
\boxed{Q[f_{m,a}]\le\frac{22}{N_a^2Z_{m,a}},\qquad
\lambda_a\le\frac{22}{N_a^2Z_{m,a}}.} \tag{S14}
\]
An inverse of a proved positive **reference** matrix appears here. No inverse, floor, or positivity assumption about Q on the full complement appears.

### 2.2 The first unpaid coefficient inequality

A sufficient, fully explicit remaining statement for the construction (S12) is
\[
\boxed{\begin{gathered}
\exists M>0,\ \nu\ge0,\ a_*>0,\ m:[a_*,\infty)\to\mathbb Z_{\ge0},\\
\forall a\ge a_*:\quad
\ell_{m(a),a}^*H_{m(a),a}^{-1}\ell_{m(a),a}
\ge\frac{22}{M e^{\nu a}T(a)^2N_a^2}.
\end{gathered}} \tag{S15}
\]
Every entry of H and ell has been specified before this inequality. The missing theorem is quantitative growth of this inverse-moment functional, not existence of the finite solve. Taking a least m satisfying (S15) would be a valid schedule only after proving that such an m exists at every sufficiently large a; it is not an existence proof by definition.

(S15) is stronger than the signed-Q mechanism because (S10) discards cancellation. Failure of (S15) for this reference construction must not kill the requested source upper-rate law. Section 3 retains the exact signed alternative.

### 2.3 Entries can be reduced to explicit theta moments

This construction is not an unknown-ground-vector prescription. To expose its coefficients, for alpha in {9/2,5/2} put
\[
P_{0,\alpha}(s)=1,\quad
P_{r+1,\alpha}(s)=(\alpha-2s)P_{r,\alpha}(s)+2sP'_{r,\alpha}(s).
\]
Then
\[
\partial_x^r(e^{\alpha x}e^{-\pi n^2e^{2x}})
=e^{\alpha x}e^{-\pi n^2e^{2x}}P_{r,\alpha}(\pi n^2e^{2x}). \tag{S16}
\]
If P_r=sum_j a_{r,j}s^j, its exact finite recurrence is
\[
a_{r+1,j}=(\alpha+2j)a_{r,j}-2a_{r,j-1},\qquad
\deg P_r=r,\quad a_{r,r}=(-2)^r,
\]
with absent coefficients set to zero. The g_{2j} row uses P_{2j+2}-P_{2j}/4, retaining both theta summands and every n.

Products in H reduce, after finite polynomial expansion and the absolutely convergent theta sums, to
\[
\int_a^\infty e^{\beta x}e^{-c e^{2x}}dx
=\frac12 c^{-\beta/2}\Gamma(\beta/2,c e^{2a}),
\quad c=\pi(n^2+l^2)>0. \tag{S17}
\]
The two tails are equal; the trace entries in (S9) are explicit endpoint series. The alpha_j use the corresponding finite-interval integrals. Thus (S15) is an inequality on an explicit finite matrix of convergent source moments. No value of a zeta zero or a window ground vector is an input.

This also identifies the loss under increasing m. Fixed-r derivative asymptotics are not uniform when r grows. The recurrence generates high polynomial powers and rapidly growing coefficients; conditioning of H and the cancellation in its inverse must be controlled together. Fixed theta truncation at n=8, or a fixed derivative-order tail estimate, is not a uniform certificate for m(a) tending to infinity.

### 2.4 What can and cannot be said about m(a)

Recomputing the leading tail integral with Y=e^{2a} gives
\[
T(a)\sim\frac{2\pi^3}{\|\Phi\|_2^2}e^{7a}e^{-2\pi Y},
\qquad T(a)^2\sim\frac{4\pi^6}{\|\Phi\|_2^4}e^{14a}e^{-4\pi Y}. \tag{S18}
\]
For fixed derivative order, the n=1 term controls the positive tail and the remaining terms are dominated; this calculation alone supplies no growing-degree estimate.

There is nevertheless a stronger unconditional baseline than D17. The same endpoint integrations give, with I=||Phi||_2^2,
\[
\mathcal W[t_a]=O(e^{2a}IT),\quad
\|1_{|x|>a}\Phi'\|_2^2=O(e^{4a}IT),\quad
|\Phi(a)|^2+|\Phi(-a)|^2=O(e^{2a}IT).
\]
Substitute these into the scaled majorant (S9). It gives B_a[Phi]<=C e^{2a}IT eventually, because a+1=O(e^{2a}). The admissible coefficient vector (1,0,...,0) shows 1/Z_{m,a}<=B_a[Phi] for every m. Therefore there exist constants C>0,a_0>0, independent of both a and m, such that
\[
\boxed{\forall a\ge a_0\ \forall m\ge0:\quad
Q[f_{m,a}]\le C e^{2a}\frac{T(a)}{1-T(a)},\qquad
\lambda_a\le C e^{2a}\frac{T(a)}{1-T(a)}.} \tag{S18b}
\]
This improves the polynomial loss in the older exp(4a)T upper bound. It still has only one factor of T, not T squared. The derivation uses a proved translation estimate at the natural tail width rather than extending the derivative bound up to t=1. [COFINAL_FAMILY][PAPER]

For illustration of a **conditional degree implication**, suppose an independently proved estimate for a normalized construction were
\[
\mathfrak B_a[v_{m,a}]/N_a^2
\le C e^{ca}T(a)e^{-\sigma m}\quad(a\ge a_0,m\ge0),\qquad \sigma>0,
\]
where C>0, c is real, and all constants are independent of both a and m. Then the explicit sufficient rounding rule would be
\[
m(a)=\max\left\{0,\left\lceil
\frac{\log(22C/M)+(c-\nu)a+\log(1/T(a))}{\sigma}
\right\rceil\right\}. \tag{S19}
\]
It has leading size (2pi/sigma)e^{2a}, not ca. This implication is elementary, but its displayed uniform contraction hypothesis has **not** been proved for our H-matrices. It is not inserted as a new supplier assumption. A linear-in-a degree under only geometric contraction would save merely exp(-O(a)), which cannot supply the extra exp(-2pi e^{2a}). This rejects that inference, not every possible true linear degree law based on a stronger mechanism. No minimal, sharp, or sufficient cofinal degree law is claimed here.

There is an exact finite-projection obstruction as well. Legendre degrees below K contain ceil(K/2) even functions. After removing the projected even p, their even complement has dimension at most ceil(K/2)-1. Thus a projected copy of all m+1 independent d_j cannot preserve rank if
\[
m+1>\lceil K/2\rceil-1. \tag{S20}
\]
At K=36 the ceiling is 17 directions; at K=48 it is 23. The labels g0-g4, g0-g8 and g0-g12 mean respectively 3,5,7 even directions, not 5,9,13. Fixed K is not a cofinal realization of growing m.

**FIRST_FAILURE Q1:** (S15), or a genuinely signed substitute from Section 3, lacks an all-a coefficient/tail estimate. Increasing degree moves the difficulty into simultaneous large-a/large-degree bounds, tail-series control, and physical-basis conditioning.

**Preserved:** Q, E, physical L2 normalization, support, every g_{2j}, antilinear-first pairing, both poles, the even upper-trial subclass. **Lost only in (S10)-(S15):** signed source cancellation, making that candidate sufficient but potentially too strong.

**Cheapest falsifier:** for an existing projected candidate freeze m=6, a=0.70 and the diagnostic envelope epsilon=T(a)^2 before further evaluation; test the unnormalized margin epsilon-Q[p-z], not q/lambda_1. The exact threshold is zero, with the total-error guard in Section 8. A negative upper enclosure refutes that degree/candidate/budget, not the existence of other constants or a cofinal schedule. Separately (S20) is a zero-cost rank falsifier for any purported growing-degree certificate on a fixed K cache. No new test was run.

## 3. RESULT Q2 — PARTIAL_WITH_PRECISE_REMAINDER

**Quantified target:** the constants, schedule and construction in Q1 must satisfy J_a(z_a)>=r_a-epsilon_a for every a>=a_*. The following identities hold for every a>0 and every finite m, without complement positivity. The missing part remains the cofinal signed inequality. Inputs: [D, D7-D8,D22-D24], [S, (2)-(7)] as RELAY rederived below, and [O]'s physical Gram convention. [ABSTRACT][PAPER; COFINAL_FAMILY][CONDITIONAL for the target]

### 3.1 Exact one-direction identity and determinant

Let d be a global radical combination with d_cut perpendicular to p; write d_out=d-d_cut. Since Phi=Np+t and Q(d,.)=Q(Phi,.)=0,
\[
r_a=\frac{Q[t]}{N^2},\qquad
Q(d_{\rm cut},p)=-\frac{Q(d_{\rm cut},t)}N
=\frac{Q(d_{\rm out},t)}N,\qquad
Q[d_{\rm cut}]=Q[d_{\rm out}]. \tag{S21}
\]
All functions belong to E by Section 1.3. The two minus signs in the middle identity cancel. No conjugation is suppressed: Q(cd,p)=conj(c)Q(d,p).

Put u=Q[d_cut], s=Q(d_out,t). For u>0, the scalar choice z=(s/(Nu))d_cut gives
\[
J_a(z)=\frac{|s|^2}{N^2u},\qquad
Q[p-z]=\frac1{N^2}\left(Q[t]-\frac{|s|^2}{u}\right). \tag{S22}
\]
Therefore the requested sufficient determinant inequality is exactly
\[
\boxed{|s|^2-u\{Q[t]-\epsilon_aN^2\}\ge0.} \tag{S23}
\]
It is a lower bound on recovered energy, not an upper bound on an inverse. It survives the source/domain audit; its cofinal sign is not proved.

### 3.2 Full finite Gram identity and deterministic signed response

Use (S7) and set
\[
C_{ij}=Q(d_i,d_j)=Q(e_i,e_j),\quad
s_i=Q(e_i,t),\quad b=s/N,\quad \tau=Q[t],\quad r=\tau/N^2.
\]
For every c in C^{m+1}, z=sum_j c_jd_j,
\[
\begin{split}
J_a(z)&=2\Re(c^*b)-c^*Cc,\\
Q[p-z]&=r-2\Re(c^*b)+c^*Cc,\\
\|p-z\|_2^2&=1+c^*Gc,\\
Q[p-z]&=\frac1{N^2}Q\left[t-N\sum_jc_je_j\right]. \tag{S24}
\end{split}
\]
The last line follows because Phi-N sum c_jh_j is global radical and its inside part is N(p-z). This is the exact residual tail, with the physical normalization still attached.

If C is positive definite on this **finite** span, define c_Q=C^{-1}s/N. This is a deterministic source construction using the full window form, not a ground eigenvector. Completing the finite square proves
\[
\begin{split}
\delta_{m,a}&=\tau-s^*C^{-1}s,\\
Q[p-\textstyle\sum c_jd_j]
 &=\frac{\delta_{m,a}}{N^2}+(c-c_Q)^*C(c-c_Q),\\
\det\begin{pmatrix}\tau&s^*\\s&C\end{pmatrix}
 &=\det(C)\,\delta_{m,a}. \tag{S25}
\end{split}
\]
Hence the first unpaid exact signed inequality is
\[
\boxed{\delta_{m(a),a}\le M e^{\nu a}T(a)^2N_a^2
\quad\text{on every positive-block window in the proposed cofinal construction}.} \tag{S26}
\]
Equivalently the bordered determinant is at most epsilon_a N_a^2 det(C). This statement concerns the signed-optimal coefficients c_Q. For the always-defined reference construction c_B from (S12), the exact strong budget instead is
\[
\delta_{m,a}+N_a^2(c_B-c_Q)^*C(c_B-c_Q)
\le\epsilon_aN_a^2. \tag{S26b}
\]
The extra nonnegative term must not be omitted when using that particular construction. (S15) is a sufficient route for it, whereas (S26) gives a potentially better, different legal source trial. Both constructions remain in the same frozen S_{m,a}; they are not silently identified.

Independence of the physical vectors proves G>0; it does not prove C>0, det(C)>0, or a uniform lower eigenvalue for C.

At fixed a, enlarging a positive restricted span cannot increase the minimized unnormalized energy: the smaller candidate set is included in the larger one. This monotonicity gives no decay rate, no termination threshold, and no uniform a-bound.

### 3.3 Infinite tail prime sums and full-source cancellation

Window-window pairings have no overlap at translations with |t|>=2a. Their prime sum therefore ends at n<=exp(2a), with a zero overlap if equality holds. This support statement does **not** apply to Q(e_i,t) or Q(e_i,e_j). Their tails are noncompact.

An explicit optional truncation bound, for integer R>=2 and u,v in E, is
\[
\left|\sum_{n>R}\frac{\Lambda(n)}{\sqrt n}
 (\langle u,U_{\log n}v\rangle+\langle u,U_{-\log n}v\rangle)\right|
\le\frac{4\log R+8}{\sqrt R}\sqrt{\mathcal W[u]\mathcal W[v]}. \tag{S27}
\]
Use (S2)'s translation estimate and sum_{n>R} log(n)n^{-3/2}<=int_R^infinity log(x)x^{-3/2}dx. This proves convergence and a source error budget. It does not assert that truncation at R=exp(2a) is small enough at T-squared scale. One can instead evaluate the equal window pairings exactly; the analytical tail identity still retains the full source.

For Q=A-P+R_pole, b=b_A-b_P+b_R. On C>0 its recovered energy is
\[
b^*C^{-1}b=S_{AA}+S_{PP}+S_{RR}
-2\Re S_{AP}+2\Re S_{AR}-2\Re S_{PR},\quad
S_{ij}=b_i^*C^{-1}b_j. \tag{S28}
\]
C itself contains all three source pieces. The scalar plant C=1, b_A=b_P=1, b_R=0 has total recovered energy zero and prime-only energy one. Dropping the mixed term fabricates a margin. The mass term vanishes from b_A by physical orthogonality, but not from C or r.

### 3.4 Nonpositive and singular branches: do not force an inverse

If a coefficient vector v has v*Cv<0, then the corresponding nonzero direction has a negative Rayleigh quotient, so lambda_a<0. It also permits the stronger affine target: rotate v so Re(v*b)>=0 and take z=t sum v_jd_j. With d=-v*Cv>0,
J_a(z)=2t Re(v*b)+dt^2; a finite source-defined t such as 1+sqrt(max(r-epsilon,0)/d) suffices. A negative rational coefficient direction can be selected by the first hit in a fixed enumeration; no full ground vector is needed.

If C is positive semidefinite and singular, distinguish two cases. If b has a nonzero component in ker(C), a null vector with nonzero coupling gives J growing linearly after phase choice. If b belongs to ran(C), then
\[
\sup_c J_a(\textstyle\sum c_jd_j)=b^*C^\dagger b,
\]
where C^dagger is the finite Moore-Penrose inverse. The strong target still requires r-b*C^dagger b<=epsilon. A null direction alone does not supply it.

Here is an exact counterexample including a global radical. On C^3 take
\[
Q[x]=|x_0-x_2|^2,\quad V=\operatorname{span}\{e_0,e_1\},
\quad \Phi=e_0+e_2,\quad p=e_0,\quad t=e_2,\quad d=e_1.
\]
Phi and d are global radical, d is physically perpendicular to p, r=1, C=0 and b=0. The normalized floor on V is zero, but J_a(cd)=0 for all c. Thus J>=r-epsilon is impossible for epsilon=1/2. This refutes only the general implication
“nonpositive direction implies the strong affine budget.” It does not refute the actual theta-source law. [ABSTRACT][PAPER]

Finally, for any actual candidate, the normalized upper inequality is
\[
r-2\Re(c^*b)+c^*Cc\le\epsilon(1+c^*Gc), \tag{S29}
\]
whereas Q2 asks for the same left side <=epsilon. These are different tests. A small normalized quotient with a large correction norm does not prove (S26).

**FIRST_FAILURE Q2:** the finite identities (S21)-(S25) close, but (S26) has not been proved cofinally. The source-independent reference candidate gives (S14), not (S26). On a null-decoupled branch, the weaker upper bound closes but the stronger affine target remains a separate demand.

**Preserved:** full Q and all mixed terms, global radical before cutting, both endpoints, physical Gram, complex conjugation, exact strong/weak budgets. **Not assumed:** full-complement positivity, positive C on every large window, or a smallest-gap estimate.

**Cheapest falsifier:** the signed margin (S23), or epsilon-Q[p-z] in (S24), has exact threshold zero. A certified upper value below zero rejects only that direction/degree/budget. Run the explicit null-decoupled plant first: any detector reporting strong success at epsilon=1/2 is invalid. No numerical plant or cache solve was executed in this audit; its algebra is exact.

## 4. RESULT Q3 — PARTIAL_WITH_PRECISE_REMAINDER

**Quantified target:** for the same source-defined f_a=p_a-z_a and the same constants and schedule, establish Q[f_a]<=epsilon_a, or explicitly distinguish the weaker Q[f_a]<=epsilon_a||f_a||_2^2. Neither T-squared budget is established here. The following identity and regularity statements hold for every fixed a,m and the source coefficients in (S12), as well as for each legal signed-response branch. [FINITE_CELL][PAPER; COFINAL_FAMILY][CONDITIONAL for the budget]

Inputs: full Q from [D, D2]; the RELAY formula [S, (8)-(9)] is rederived, not treated as a theorem. [S26]'s source functional independently checks the prime and pole signs.

### 4.1 An explicit autocorrelation for the actual construction

For c_j=-theta_{j+1}/N in (S12), or any finite source c, write
\[
v(x)=\left(N^{-1}+\sum_jc_j\alpha_j\right)\Phi(x)-\sum_jc_jg_{2j}(x),
\qquad f(x)=1_{(-a,a)}v(x). \tag{S30}
\]
This is an explicit smooth inside representative. No unknown minimizing eigenfunction appears. For 0<=t<=2a,
\[
R_f(t)=\Re\int_{t-a}^{a}\overline{v(y)}v(y-t)dy,
\quad R_f(-t)=R_f(t),\quad R_f(t)=0\ (|t|\ge2a). \tag{S31}
\]
For example, if beta=(N^{-1}+sum c_j alpha_j,-c_0,...,-c_m), then
R_f(t)=Re sum_{i,j} conj(beta_i)beta_j int_{t-a}^a u_i(y)u_j(y-t)dy. This retains every mixed source coefficient.

Leibniz differentiation gives for 0<t<2a
\[
R_f'(t)=-\Re\{\overline{v(t-a)}v(-a)\}
-\Re\int_{t-a}^{a}\overline{v(y)}v'(y-t)dy. \tag{S32}
\]
The first term is the moving-boundary trace. It cannot be dropped because f was sharply cut. The derivative is bounded by ||v||_infty^2+||v||_2||v'||_2 on the fixed inside interval. Thus R_f is absolutely continuous on [0,2a], even though f need not be in global H1. A cusp at zero is allowed; no derivative value at that single point is used.

### 4.2 Stieltjes integration by parts, including both ends

Set X=exp(2a),
\[
k_a(x)=x^{-1/2}R_f(\log x),\quad
k_a'(x)=x^{-3/2}\{R_f'(\log x)-\tfrac12R_f(\log x)\},
\quad1<x<X. \tag{S33}
\]
This k is absolutely continuous on [1,X], k(X)=0, and k(1)=||f||_2^2. Let
psi(x)=sum_{n<=x}Lambda(n), including every prime power, and D_psi(x)=psi(x)-(x-1). There is no atom at 1 and D_psi(1)=0. Therefore
\[
\begin{split}
\sum_{2\le n\le X}\Lambda(n)k_a(n)
&=\int_{[1,X]}k_a\,d\psi\\
&=\int_1^X k_a(x)dx-\int_1^X D_\psi(x)k_a'(x)dx. \tag{S34}
\end{split}
\]
The boundary term k(X)D_psi(X)-k(1)D_psi(1) is exactly zero. If X is a prime power, its endpoint atom is multiplied by k(X)=0, so the inclusive cutoff is harmless. Only absolute continuity of k and bounded variation of D_psi on this finite interval are used.

Writing
\[
\mathcal A[f]=\mathcal D[f]-c_A\|f\|_2^2,
\qquad R_{\rm pole}[f]=2\Re(\overline{M_+(f)}M_-(f)),
\]
we obtain exactly
\[
\boxed{Q[f]=\mathcal A[f]+R_{\rm pole}[f]
-2\int_1^X k_a(x)dx+2\int_1^X D_\psi(x)k_a'(x)dx.} \tag{S35}
\]
The archimedean term can itself be evaluated from (S31):
D[f]=2 int_0^infinity A_0(t)(||f||_2^2-R_f(t))dt. Near zero the difference is O(t), so its singular integral is legitimate. For our real-even construction M_+=M_- and the pole term is twice their square; it does not vanish in general.

### 4.3 The first unpaid signed integral, not a prime-only estimate

Define the fully specified main term
\[
\mathcal M_a=\mathcal A[f_a]+R_{\rm pole}[f_a]-2\int_1^Xk_a(x)dx.
\]
With v as in (S30), the remaining signed term is
\[
\begin{split}
\mathcal I_a=2\int_1^X D_\psi(x)x^{-3/2}\Bigl[
&-\Re\{\overline{v(\log x-a)}v(-a)\}\\
&-\Re\int_{\log x-a}^{a}\overline{v(y)}v'(y-\log x)dy
-\tfrac12R_f(\log x)\Bigr]dx. \tag{S36}
\end{split}
\]
Its exact unpaid inequalities are
\[
\boxed{\mathcal I_a\le M e^{\nu a}T(a)^2-\mathcal M_a}
\quad\text{for the strong Q2 budget}, \tag{S37}
\]
and
\[
\boxed{\mathcal I_a\le M e^{\nu a}T(a)^2(1+c^*Gc)-\mathcal M_a}
\quad\text{for the normalized upper budget}. \tag{S38}
\]
They must hold for every a>=a_* on one fixed schedule and coefficient construction. We have proved neither. The bound (S14) supplies a different unconditional upper envelope for the reference construction; replacing it by T-squared would require (S15).

For any proposed absolute prime-counting envelope |D_psi|<=E_psi, a sufficient replacement is
\[
\mathcal M_a+2\int_1^X E_\psi(x)|k_a'(x)|dx
\le\epsilon_a\quad\text{or}\quad\epsilon_a(1+c^*Gc), \tag{S39}
\]
respectively. No prime-number asymptotic by itself establishes (S39). The moving-boundary term, the coefficient growth, and cancellation between I_a and M_a all remain in the ledger. In particular a positive upper estimate for the last integral is not a negative error estimate for the total form.

**FIRST_FAILURE Q3:** (S37), or the weaker (S38), is not bounded at its required T-squared scale. Formula (S36) is the first unpaid signed source integral, with its kernel, domain, coefficients and budget explicit.

**Preserved:** every prime power, both pole terms, the -c_A mass term, all mixed coefficients, sharp-cut trace and exact physical norm. **Lost if one uses (S39):** signed arithmetic cancellation. No such loss is made in (S35)-(S38).

**Cheapest falsifier:** for the same frozen cached candidate, compare the full-form energy with the Stieltjes/autocorrelation energy before testing a sign. Their difference must lie in its independently computed total-error interval; use a discrepancy exceeding 10 times that bound as the diagnostic rejection threshold. The final strong or weak margin has exact threshold zero. Without the error bound, report UNRESOLVED rather than calling an identity or a mechanism false. No new arithmetic run is authorized or performed here.

## 5. Strongest attacks and what is genuinely new

The strongest objection is that (S15) might be just as difficult as (S26), or stronger. That objection is accepted. The new result is not a concealed rate theorem: it is a source-defined positive finite moment problem which always constructs an admissible trial, together with the explicit coefficient inequality needed to spend it. Its advantage is that inverse existence is unconditional and the entries reduce to theta moments. Its disadvantage is loss of the signed Q cancellation. [ABSTRACT][PAPER; COFINAL_FAMILY][CONDITIONAL]

The other major objection is the hidden inference from cofinal complement positivity. It is indeed forbidden. If a_j tends to infinity and Q is nonnegative on K_{a_j} eventually, then p_{a_j} tends to Phi/||Phi||_2 in E. For each fixed compact smooth f, put h_j=f-<p_{a_j},f>p_{a_j}. Eventually h_j belongs to K_{a_j}; the coefficients remain bounded. Radical membership and (S2) give Q[h_j] tending to Q[f]. Thus Q[f]>=0 for every compact smooth f. Such complement positivity would already provide the unchanged global sign. We have used only positivity of G and of the independent reference H, not this premise. [COFINAL_FAMILY][PAPER]

Three claims in the diagnostic prose are not accepted as theorems: a few sampled windows cannot show that no fixed direction ever works cofinally; small q/lambda_1 does not establish the strong J budget; and min spectrum of a complement is not identically lambda_2 merely because a matrix is Hermitian. It requires the appropriate invariant sector or additional spectral argument. Reported floating agreements remain diagnostics. [FINITE_CELL][PAPER for the scope audit]

## 6. Route map and consumer-first dependency contract

| Representation | Preserves / loses | Main risk | Kill-power / cost estimate | Status |
|---|---|---|---|---|
| Full signed finite tail response (S24)-(S26) | Preserves Q and all cancellation; retains actual C inertia and G | Uniform degree and signed bordered remainder | 9/10; 7/10 | Algebra proved; rate open |
| Positive theta-tail moment construction (S9)-(S17) | Same source trial class and norm; majorant loses signed cancellation | Inverse-moment growth may be too weak | 8/10; 6/10 to test, larger to prove uniformly | New constructive upper envelope; T-squared rate open |
| Boundary-jet matching of a radical combination | Same derivative class if coefficients are source-derived | A jet-system inverse and an outside remainder must both be controlled | 8/10; 8/10 | Candidate only; not substituted for a proof |

These estimates rank proof work, not mathematical probabilities or execution authorization.

```yaml
K8A:
  DOWNSTREAM_CONSUMER: published_Weil_criterion_on_all_complex_compact_smooth_tests
  ACTUAL_CONSUMER_REQUIREMENT: Q_nonnegative_on_every_such_test
  ORIGINAL_REQUESTED_OBJECT: source_defined_T_squared_window_upper_rate
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACES:
    - an_all_large_window_lower_envelope_lambda_a_ge_minus_epsilon_a_with_epsilon_a_to_zero
    - direct_nonnegativity_on_the_compact_smooth_core
  UPPER_RATE_IMPLICATION: controls_a_trial_above_the_minimum_only_not_the_lower_sign
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: positive_tail_moment_construction_with_exact_signed_Schur_and_arithmetic_comparison
  REOPEN_TRIGGER: uniform_proof_of_S15_or_S26_or_direct_S37_for_one_fixed_source_schedule
SCOPED_REFUTATION:
  CLAIM: nonpositive_direction_automatically_pays_the_strong_affine_J_budget
  KILL_SCOPE: THEOREM_SHAPE
  KILL_EVIDENCE_KIND: exact_radical_compatible_three_dimensional_counterexample
  EVIDENCE: section_3_4_of_this_verdict
  FAILURE_TYPE: COUNTEREXAMPLE
  EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
  ACTUAL_THETA_SOURCE_COUNTEREXAMPLE: false
CLOSES:
  - global_radical_orthogonalization_and_tail_identity_on_the_chosen_finite_spans
  - exact_physical_rank_and_reference_inverse_existence
  - strong_vs_normalized_budget_and_null_branch_ambiguity
  - autocorrelation_regularities_and_endpoint_terms_for_the_constructed_trial
CLOSES_COFINAL_RATE_SUPPLIER: false
OPENS: []
CARRIES_OPEN:
  - cofinal_degree_and_coefficient_tail_bound
  - full_source_T_squared_upper_rate
  - all_large_window_lower_sign_envelope
```

In particular, proving an upper bound tending to zero does not prove a lower bound tending to zero. The sign blocker has not moved or been assumed.

## 7. Frozen predictions and meta closeout

| Frozen event | Fate | Scope of the score |
|---|---|---|
| P_DEGREE_UNPAID, 0.70 | CONFIRMED | No proved cofinal law with fixed constants; (S15)/(S26) remains. |
| P_DETERMINANT_INTERFACE, 0.90 | CONFIRMED | (S21)-(S25) survive; their cofinal inequality remains unpaid. The singular-branch qualification does not alter the positive-direction determinant. |
| P_ARITHMETIC_REMAINDER, 0.80 | CONFIRMED | Explicit v, R, k, k' and signed integral (S36) are derived; neither T-squared budget is paid. |
| P_UPPER_NOT_SIGN, 0.99 | CONFIRMED | No upper-rate result in this batch supplies the all-support lower sign. |
| q/lambda_1=1.5 at a=0.75, K=48, g0-g12 | UNRESOLVED | The authorized packet supplies no total-error-resolved outcome; no new run was performed. |

These score the requested events in this response, not correctness certified by an independent prover. No forecast definition or probability was revised.

What became smaller: a source-only finite coefficient recipe and two explicit remainder tests replace an unspecified choice of correction. What is not closed: any cofinal T-squared rate. What must not recur: dropping the mixed source terms, treating an indefinite stationary solve as a positive Schur optimizer, or using a small normalized quotient to claim the stronger affine budget. [ABSTRACT][PAPER]

The unconditional baseline also improves from polynomial-times-exp(4a)T to the bound (S18b). This does not deliver the extra T. The useful numerical discovery is directional recovery of energy, not a proof of a degree law. The exact new finite rank result also distinguishes genuine source independence from loss of rank in a fixed Legendre projection. The smallest unresolved analytical interface is the simultaneous a,m estimate (S15) for the positive reference construction, or its weaker signed counterpart (S26). [COFINAL_FAMILY][CONDITIONAL]

```yaml
iteration:
  target: GOAL058_RADICAL_TRIAL_SCHUR_T_SQUARED_SUPPLIER
  status: OPEN
  progress_class: REPRESENTATION_PROGRESS
  cognitive_operator_used: MINIMAL_LEMMA
  failed_strategy: infer_cofinal_rate_or_strong_affine_success_from_finite_normalized_ratios
  invariant_learned: physical_rank_is_positive_but_signed_form_rank_and_sign_are_separate
  forbidden_future_move: use_full_complement_positivity_to_justify_a_cofinal_inverse
  next_decisive_test: error_resolved_full_source_strong_margin_on_a_frozen_cached_candidate
  route_score: 4
```

## 8. One next_decisive_test and delivery handoff

**One test only: an error-resolved unnormalized margin for a frozen source trial.** Use an already existing K=36, a=0.70, m=6 candidate, or an already completed matching K=48 record if it is supplied with immutable binding and total errors. This is a proposed handoff, not a new numerical run or execution grant. Do not mix a K=48 matrix with the hard-coded K=36 coefficient constructor in [O].

Freeze the coefficients and the finite diagnostic envelope **M_diag=1, nu_diag=0**, so epsilon_diag=T(0.70)^2. This is not a claimed cofinal choice of M,nu. Test
\[
\mathfrak m=\epsilon_{\rm diag}-Q[p-z]. \tag{S40}
\]
Register the exact sign threshold **0** and the robustness threshold **10 times total absolute uncertainty**. These are prospective execution thresholds, not blinded forecasts: the packet already contains approximate ratios. Report the normalized margin separately, never in place of (S40).

Evaluate a frozen candidate as a vector, rather than depending on a numerically unstable inverse to certify optimality. If w=(1,-c) is its coefficient vector in the augmented physical basis, a componentwise builder bound |Delta Q_ij|<=E_ij contributes at most |w|^T E |w|. Add the row-wise floating summation bound and the source/projection error. If ||f-f_tilde||_E<=e, (S2) supplies the latter contribution
\[
22e(2\|f_{\rm tilde}\|_E+e). \tag{S41}
\]
The normalization of p, theta-series truncation, quadrature, Fourier-tail correction and basis projection must all be included. Settings XI=20000 and h=0.02 are not themselves these bounds. K-stability does not establish them either. Without an actual E or builder error budget the row is UNRESOLVED, regardless of printed digits.

**ЕСЛИ_A:** a lower enclosure for (S40) is nonnegative and the total uncertainty is at most one tenth of the resolved margin. Admit only this finite candidate and this finite budget. Use its coefficients to discriminate a signed-tail mechanism from the positive-reference majorant; a separate all-a proof is still required.

**ЕСЛИ_B:** a strict upper enclosure for (S40) is negative with the same error separation. Reject that candidate/degree/budget and retain the full signed tail and arithmetic ledgers. Do not infer a failure of the actual-source T-squared law. If the enclosure contains zero, or total uncertainty is unavailable, the result is UNRESOLVED and no mechanism failure is scored.

The exact null-decoupled plant in Section 3.4 must not be misclassified as strong success. For the numerical 1.5 forecast, division by lambda_1 is allowed only after its total-error enclosure excludes zero; this verdict has no such certified denominator.

**Repository handoff:** only the expected verdict path may be added. No Lean, queue or state edit is included. No `lake` or axiom-profile gate applies to this documentation-only artifact. A delivery worker must first complete the eight outstanding shelf SHA checks from the pinned Git objects, inspect this paper proof independently, add this exact file at EXPECTED_VERDICT_PATH, and record its resulting commit, blob and SHA-256. Publication checks certify bytes, not (S15), (S26), (S37), or the sign.

## 9. Proshka's own line

I keep the signed tail response because it measures the energy that must actually be recovered.
The physical norm constraint is what prevents the radical from solving a different, trivial problem.
The positive reference construction gives a second route without assuming a sign for Q.
Its coefficients depend only on explicit theta moments and endpoint traces.
That is useful even if its upper envelope ultimately proves too expensive.
I did not choose a full-complement inverse as the starting point.
Proving its cofinal positivity would already spend the global sign that this batch must not assume.
I also did not choose a degree law by extending the finite table.
A few nearby windows cannot separate linear, exponential, or threshold-dependent degree growth.
The first move beyond this batch is to resolve the strong signed margin for one frozen coefficient row.
An error-resolved negative margin would kill that row and budget immediately.
It would not kill a higher-degree or differently constructed source row.
The second move is to compare that row with the positive theta-tail moment minimizer.
A large reference cost with a small signed energy would show that cancellation, not tail size alone, is essential.
That would stop investment in the absolute-majorant route before a long formalization effort.
The most useful missing data are actual coefficient rows with physical Gram information and absolute errors.
I would ask for those before another ratio against a very small eigenvalue.
I would also ask for the norm of the correction, since the strong and normalized budgets differ by it.
The exact independence of all finite radical derivative cuts is a useful structural fact.
The corresponding projected Gram can nevertheless lose rank at fixed K.
The sharp-cut autocorrelation was less troublesome than a global H1 formulation would suggest.
Its moving-boundary trace is explicit and its Stieltjes endpoints vanish exactly.
I distrust claims that an inverse solve or a small residual automatically certifies a tiny final energy.
I also distrust fixed theta truncations when the derivative order is allowed to grow.
The promising part is that the remaining estimates now have explicit coefficients, endpoints and budgets.
The unresolved part is precisely their simultaneous control as both the window and degree grow.

## 10. Research log

### 10.1 Sources consulted and use

Repository locators are the exact paths, commit and blobs in Section 0, not moving-branch substitutes.

| Source | READ / RELAY | Exact material taken or rejected |
|---|---|---|
| Authoritative SCHUR request, commit e11338a3a9132c88895b565d74ce189503d1c642 | READ in full; request hashes recomputed | Three proof obligations, fixed trial class, full source, result schema, forecasts and write boundary. |
| PROSHKA_SYSTEM_PROMPT_v2.md, blob eba04b799176c9e6a1d5f7fc4061280cfbf96ad4 | READ | Current intake, proof/evidence distinctions and append-only verdict format. |
| [B] BATCH_PATTERNS | READ | Proof-batch requirement: a named remainder must follow an attempted derivation, not replace it. |
| [D] DISTANCE, D2-D8,D15-D24; D29-D36 and closeout | READ, prior paper derivation rechecked where used | Full form/domain, theta normalization, legal cuts, radical identity, T exponent and the unpaid Schur target. No old rate promoted to a theorem. |
| [I] independent check, D2-D24 and diagnostic/scoring discussion | READ | Source-normalization cross-check and known finite diagnostics. Its mpmath/numpy tests are not interval or universal certificates. |
| [S] point-5 supplement, (2)-(10) | RELAY, text read | Recovered-energy, tail forcing and arithmetic formulas rederived in Sections 3-4; the null-decoupled qualification is added explicitly. |
| [A] addendum, points 1-5 | READ diagnostic report | D37 and full-response observations, pending-run boundary; no certified cofinal inference. |
| [W] window-tail probe, readings and final span table | READ | Exact span labels and diagnostic failure modes. Its finite-to-cofinal prose and min-spec-C equality are not admitted as general theorems. |
| [O] one_direction_margin.py | READ in full, NOT executed | Exact recurrence, physical projection, hard-coded K=36, theta truncation at 8; span solve computes a stationary point even when C is not proved positive. |
| [V] window_derivative.py | READ in full, NOT executed | Saved Q/G/eigenpair/cut-Phi structure, finite projection and raw normalization. The docstring's F_Phi=Xi is not the exact request normalization. |
| [C] sc_build.py | READ in full, NOT executed | Archimedean Fourier symbol, finite prime overlaps, both pole moments and numerical-tail settings. Gaussian quadrature exactness for polynomials does not eliminate floating or other builder errors. |
| [K] KERNEL, K6-K18,K24-K26 | READ relevant source/domain proofs | Continuity and signed radical convention. K18 uses twice the present Phi; the distinction is retained. The pole-null Riesz realization is not imported as a full-E positivity theorem. |
| [S26] Masatoshi Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096v2, HTML `https://arxiv.org/html/2606.09096v2`, introduction functional and (3.1) | READ primary HTML | Source and signed explicit formula only. Convert linear-first pairing and Fourier variable; its xi omits the conventional factor 1/2. No window positivity, spectral asymptotic, or cofinal estimate imported. |
| [N] NIST DLMF version 1.2.7, release 2026-06-15, `https://dlmf.nist.gov/25.4`, equations 25.4.3-25.4.4 | READ | Standard xi normalization and reflection, used to check (S3). |
| [NT] NIST DLMF version 1.2.7, `https://dlmf.nist.gov/20.7`, equation 20.7.32 | READ primary HTML | Theta inversion at z=0 and tau=iu, u>0; differentiated in Section 1.2 to verify evenness. Direct TeX fetch was unsupported; the HTML equation was read. |
| Direct raw-GitHub HTTP acquisition attempt for [B] | UNAVAILABLE, not evidence | Failed transport; connector pin remains the source. Does not certify missing shelf SHA checks. |
| GitHub write-tool discovery and installed-plugin search | READ capability metadata | No usable write action returned; the installed integration description does not constitute a commit or push. |
| `git ls-remote https://github.com/Malaeu/chen_q3.git refs/heads/rh_clean` | EXECUTED connectivity check, no repository write | Exit 128, DNS resolution of github.com failed; no clone, commit, or push occurred. |

No PDF was used in this completed continuation; no OCR, eigensolve, numerical fit, interval run or Lean execution was performed. Other articles mentioned by the shelf remain RELAY and were not imported here as independently read theorems.

### 10.2 Candidate approaches and their decisive obstacles

| Candidate | First obstacle / precise reason not promoted |
|---|---|
| Full-complement positivity before taking an inverse | The fixed-test argument in Section 5 already gives global nonnegativity from that premise. |
| Prime-only recovered energy | C=1,b_A=b_P=1,b_R=0 gives full energy zero, prime-only energy one. |
| Invert any finite C and call it the maximizing response | Completing the square maximizes J only when C is positive; negative and null branches need Section 3.4. |
| A zero direction automatically proves the strong affine target | The radical-compatible three-dimensional plant has J identically zero and r=1. |
| Derive m(a) proportional to a from a few span ratios | No all-a coefficient estimate; under merely geometric contraction the elementary threshold instead contains log(1/T(a)). |
| Use fixed-order theta asymptotics at growing derivative order | Coefficients and polynomial degrees in (S16) are not uniformly bounded in that limit. |
| Keep K=36 while m tends to infinity | Physical projected even-complement dimension is at most 17. |
| Force many boundary jets to vanish | An invertible jet matrix and a uniform outside remainder estimate have not been proved; endpoint zeros alone do not bound the entire tail. |
| Positive reference tail matrix as an automatic T-squared proof | Inverse existence is proved, but the quantitative inequality (S15) is not. |
| A generic absolute prime-counting error solves Q3 | It must still satisfy the full main-term budget (S39), including the sharp-cut boundary contribution. |

### 10.3 Reusable identities and limits of their use

(S8) gives exact physical rank for every finite source span, independently of Q's sign.
(S9)-(S14) give a positive-reference source construction and a proved explicit upper envelope.
(S16)-(S17) reduce its coefficients to recurrences and incomplete-gamma theta moments.
(S18b) is a proved unconditional exp(2a)T/(1-T) upper bound, still short of T squared.
(S21)-(S25) identify the entire finite Schur problem with its full outside-tail Gram.
(S27) is an unconditional omitted-prime-tail error bound, not a sufficient T-squared truncation rule.
(S32) gives the missing moving-boundary trace in the derivative of the sharp-cut autocorrelation.
(S35)-(S38) distinguish the exact arithmetic identity from its two different unproved budgets.
(S41) transports a finite-projection error to a full-form error without a positivity assumption.

None of these identities establishes a cofinal rate by itself. Their purpose is to make the next proof or falsifier act on the same source quantity, with no normalization or sign change.
