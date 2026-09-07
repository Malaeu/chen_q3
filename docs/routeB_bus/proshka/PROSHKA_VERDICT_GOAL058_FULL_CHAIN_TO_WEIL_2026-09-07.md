# STATUS: TRY_FULL_WEIL_SIGNED_HEAD_WITH_EXPLICIT_TAIL
```yaml
OPERATIVE_CLASS: TRY_FULL_WEIL_SIGNED_HEAD_WITH_EXPLICIT_TAIL
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-07-CHAIN
BOUNDARY_ID: GOAL058_FULL_CHAIN_FROM_THE_CLOSED_CELL_TO_THE_TERMINAL_WEIL_CONSUMER
RESULT:
  OVERALL: IRREDUCIBLE_ATOM
  Q1: IRREDUCIBLE_ATOM
  Q1a: OBSTRUCTION_NAMED
  Q1b: PARTIAL_CHAIN_WITH_NAMED_GAPS
  Q1c: PARTIAL_CHAIN_WITH_NAMED_GAPS
  Q1d: IRREDUCIBLE_ATOM
  Q2: PARTIAL_CHAIN_WITH_NAMED_GAPS
  Q3: COMPUTATION_SPECIFIED
  Q4: PARTIAL_CHAIN_WITH_NAMED_GAPS
REQUEST_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  COMMIT: 90451f79641c8b293fe3f14b03d8ec111a3f6f88
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_FULL_CHAIN_TO_WEIL_2026-09-07.txt
  GIT_BLOB: c8a0ae92c40551ca5fec6020de710beb9f73870f
  SHA256: 4cebbf31d1d823b4f4bc595f6ac439a68321ec03ab573a1140130d51113d7472
  BYTES: 10030
  LINES: 70
  FINAL_LF: true
  FETCHED_THROUGH_GITHUB_CONNECTOR: true
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
  COMPLETE_PROOF_CHAIN_ON_PINNED_SHELF: false
  COMPLETE_DEPENDENCY_CHAIN_WRITTEN: true
  FIRST_FAILURE_OF_LITERAL_P1_EXTENSION: three_lobe_mean_control
  THREE_LOBE_WEIL_FORM_REFUTED: false
  THREE_LOBE_POSITIVITY_PROVED_HERE: false
  PRIME_SUM_GROWTH_IS_THE_FIRST_P1_FAILURE: false
  ARCHIMEDEAN_ENERGY_ALONE_COVERS_ALL_POLE_NULL_SUPPORTS: false
  REPLACEMENT_SELECTED: full_geometric_Weil_form_and_its_signed_low_energy_Schur_head
  UNIVERSAL_RESERVOIR_MINORANT_ASSUMED: false
  EXPLICIT_POSITIVE_TAIL_ON_EACH_FULL_SUPPORT: PAPER_DERIVED
  FINITE_HEAD_PER_SUPPORT: PAPER_DERIVED
  SINGLE_FINITE_HEAD_FOR_ALL_SUPPORTS: not_supplied
  SOURCE_SPECIFIC_SIGN_INDUCTION_OR_UNIFORM_CERTIFICATE_RULE: not_found_not_proved
  UNIFORM_POSITIVE_L2_GAP_REQUIRED: false
  SMALL_NEGATIVE_LOWER_ERRORS_TENDING_TO_ZERO_SUFFICE: true
  WHOLE_WEIL_POSITIVITY: not_proved
ATOM:
  NAME: ALL_SUPPORT_SIGNED_SCHUR_HEAD_LOWER_BOUND
  EXACT_STATEMENT: S_n(1/n)_is_positive_semidefinite_for_every_integer_n_ge_1
  OBJECTS_DEFINED_IN: Sections_4_and_5
  SCOPE: COFINAL_FAMILY
  VERIFIER: CONDITIONAL
  STATUS: OPEN_NO_MECHANISM_for_the_universal_sign
  IRREDUCIBLE_MEANS: remaining_substantive_obligation_relative_to_this_shelf_not_a_proof_of_absolute_indivisibility
CLOSES: [REQ-2026-09-07-CHAIN]
CLOSES_ANALYTIC_RH_SUPPLIERS: []
OPENS: []
NEW_RESULTS:
  - exact_three_lobe_counterexample_to_the_P1_small_mean_bound
  - strict_failure_of_the_coarse_three_lobe_scalar_budget
  - slow_pole_null_family_with_archimedean_energy_O_R_minus_2
  - explicit_all_support_positive_tail_and_signed_finite_head_reduction
  - complete_quantifier_and_error_interface_to_the_terminal_consumer
NEW_DERIVATIONS:
  SCOPE: ABSTRACT
  VERIFIER: PAPER
  INDEPENDENT_REVIEW: pending
  LEAN_KERNEL_VERIFIED: false
EVIDENCE_BOUNDARY:
  ANALYTIC_CUTOFF: 90451f79641c8b293fe3f14b03d8ec111a3f6f88
  POST_REQUEST_PROJECT_RESULTS_USED: false
  ANOTHER_CHAIN_VERDICT_USED: false
  PROFILES_LOCAL_FILE_MATCHED_TO_PINNED_BLOB_AND_SHA256: true
  ALL_SHELF_HASH_PREFIXES_RECOMPUTED: false
  MISSING_CITED_FILE: docs/CHAIN_GAP_DESIGN.md_at_pin_returns_404
  OLD_UPLOADED_ROADMAPS_USED: false
EXECUTION:
  HASH_COMPUTATION: true
  NUMERICAL_RUN: false
  SYMBOLIC_SOFTWARE_EXPERIMENT: false
  LEAN_EDIT: false
  ARISTOTLE_SUBMISSION: false
  QUEUE_OR_SHARED_STATE_EDIT: false
PUBLICATION:
  AUTHORIZED_WRITE_SCOPE: VERDICT_DOC_ONLY
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_FULL_CHAIN_TO_WEIL_2026-09-07.md
  METHOD: GitHub_create_file_single_document
  COMMIT_AND_READBACK_BLOB: delivery_receipt
  RECEIPT_EFFECT: publication_only_not_an_independent_proof_gate
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## 0. Answer to the owner, and the evidence boundary

**I do not have a completed chain from C1/C2 to the terminal Weil consumer. My previous next-cell ranking was not such a chain.** The pinned shelf supplies two genuine restricted results and several exact representations; it supplies no source-specific rule propagating the sign to every larger support. This verdict makes that absence explicit rather than promising that a reservoir will inevitably repair the first failed estimate.

The first failure of the *literal P1 proof* is earlier and more specific than exponential prime growth. With three lobes, two pole moments leave an uncontrolled local-mean direction. Section 2 gives its exact vector and an admissible smooth witness. The obvious replacement of P1's small-mean estimate by the trivial bound produces a strictly negative **sufficient budget** already on that cell. Neither finding is a negative value of the actual Weil form. [ABSTRACT][PAPER]

There is a finite mathematical dependency chain, with exactly one unproved global sign target after the reductions below. For every support we can construct, without RH, an explicit positive infinite-dimensional tail. The remaining source object is a finite signed Schur head. A universal sign theorem for these heads would finish the chain. The shelf does not prove it, nor provide a verified induction invariant or a single positive representation that proves it for all supports. **Finite per support is not finite proof of all supports.** [COFINAL_FAMILY][CONDITIONAL]

The new tail construction is deliberately conservative; its enormous cutoff is not advertised as a practical algorithm. It isolates the quantifier honestly. The bounded proposed computation targets the first newly exposed mean/coupling sector, not that enormous cutoff.

### Sources actually used

All repository references are at the request pin unless qualified.

| Key | Source | Use and verification boundary |
|---|---|---|
| REQ | Exact request in the header | Complete UTF-8 content read; both hashes, both counts, and final LF independently checked. |
| P | PROFILES verdict, `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_INDEPENDENT_PROFILES_RESERVOIR_2026-09-07.md` | Blob `4720e7c6049107188c0247d437f38aa923bc9407`; local SHA-256 `d41d936fbe38b261dfdd6b4714a1f686051994605ca2f87c32cdf9a8457e869b` recomputed; connector confirms the same blob at the CHAIN pin. Sections 1--9 read. |
| G | GAUGE theorem as stated in P, Section 7, and REQ | Retained at its inherited PAPER plus certified-norm boundary; no new certificate rerun or silent promotion. |
| BP | `docs/BATCH_PATTERNS.md` | Blob `3b3d75ecc0d76ad0e9561db2b0c744ad584354b9`; FULL_CHAIN/atom distinction and WEILPROOF rules read in full. |
| M | `docs/METHOD_ROOF_TO_ATOM.md` | Blob `41213e8150fc3858bca0434314ece5d9fb1c64bb`; method and one-sided representation rule read in full. |
| WNY | `docs/WHY_NOT_YET.md` | Sections 1--4 and supplied current-cell discussion read as an observer diagnosis, not mathematical premises. |
| LOG | `docs/Progress_Log.md` | Header/initial entries inspected only; no unreturned independent PROFILES audit inferred from this log. |
| GAP | `docs/CHAIN_GAP_DESIGN.md` | The exact cited path returns 404. The roof/pillar/rope meanings are explicit in REQ and M; no substitute archive was used. |
| CC20 | Connes--Consani, arXiv:2006.13771v1, Introduction (1)--(2), Appendix C | Published Weil criterion and finite vanishing-constraint variant; not a global sign supplier. Primary HTML checked. |
| CCM23 | Connes--Consani--Moscovici, arXiv:2310.18423v2, Introduction, Sections 4.6--4.7 | Finite-prime setup and Sonin correspondence, not positivity uniformly in the prime set. Primary HTML checked. |
| DLMF | NIST DLMF 5.7.6, 5.4 and 27.2.3 | Digamma series/special values and the unconditional prime number theorem. New estimates below are derived here, not attributed to DLMF as ready-made lemmas. |

The task explicitly cites the four non-bus planning/log files above; no other personal archive was opened. No PDF, new numerical certificate, or Lean build was used. New proofs require independent review. A bound quoted from a parent remains conditional on that parent's identified analytic and numerical inputs.

## 1. Source lock and the full rope table

Put
\[
 A(t)=\frac{e^{-t/2}}{1-e^{-2t}},\quad
 c_A=\gamma_E+\log(8\pi)+\frac\pi2,\quad
 w_n=\frac{\Lambda(n)}{\sqrt n},\quad U_tf(x)=f(x-t).
\]
Use \(\widehat f(\xi)=\int f(x)e^{-i\xi x}dx\),
\(C_f(t)=\Re\int\overline{f(x)}f(x+t)dx\), and
\(M_\pm(f)=\int f(x)e^{\pm x/2}dx\). The literal form, with all poles retained, is
\[
 \boxed{\mathcal Q(f)=\mathcal D(f)-c_A\|f\|^2
 -2\sum_{n\ge2}w_n C_f(\log n)
 +2\Re\{M_+(f)\overline{M_-(f)}\},\quad
 \mathcal D(f)=\int_0^\infty A(t)\|U_tf-f\|^2dt.} \tag{C1}
\]
This is P (P1)--(P2). The sum is finite on every fixed compact support. All forms below are Hermitian with inner products antilinear in the first argument. Normalization is never changed to force a sign.

The **roof** is the published Weil criterion. The **pillars** are the full joint spaces
\(\mathcal D_n=C_c^\infty((-n,n);\mathbb C)\), not unions of isolated positive rays. The **ropes** are the following statements. C1 and C2 are calibration branches of the chain, not an induction hypothesis about all of \(\mathcal D_1\).

| Rope | Exact statement | Status | Mechanism | Falsifier / first failure | Tags |
|---|---|---|---|---|---|
| R1 | Equation (C1), including polarization, on every compact smooth test | PROVED_PAPER | Source explicit formula in P; Fourier/log transport | A lost pole, conjugation, or prime-power coefficient breaks source equality | ABSTRACT / PAPER |
| R2 | On the fixed minus class, \(Q(v_h)=n_2+\mathcal F(h)+\|T_vD_2\|_{HS}^2\), \(\|h\|^2\mathcal F(h)\ge\mathcal P[h]/2\) | PROVED_PAPER_PLUS_ARB | G's pole gauge and its completed two-norm certificate | Failure of a named source identity or of either outward norm bound reopens this row only | ABSTRACT / PAPER; FINITE_CELL / ARB_INTERVAL |
| R3 | On the fixed two-support total-pole-null class, \(Q(v)\ge\|v\|^2/100\) | PROVED_PAPER | P Theorem P1, equations (P17)--(P26), rechecked here | Exact moment/energy budget, not a sampling fit; independent external audit still pending at intake | ABSTRACT / PAPER |
| R4 | The copied P1 small-mean bound fails on the three-center class; its coarse rescue budget is negative | PROVED_PAPER | Explicit null vector (C2), exact witness, (C6) | This kills a sufficient proof step, not Q on the class | ABSTRACT / PAPER |
| R5 | Every compact smooth test lies in some \(\mathcal D_n\); only \(n'\le e^{2n}\) can contribute in (C1) | PROVED_PAPER | Support of autocorrelation; full pole term kept | Leaving out any mixed correlation, gap in support coverage, or treating only separated lobes violates this row | ABSTRACT / PAPER |
| R6 | For each integer n, the explicit tail \(T_n\) in Section 4 satisfies \(Q(y)\ge\|y\|^2\) | PROVED_PAPER | Cell-average orthogonality, digamma series, frequency mass bound | A low-frequency leakage factor or omitted prime term invalidates (C15) | ABSTRACT / PAPER, new |
| R7 | \(Q+\epsilon\|\cdot\|^2\ge0\) on the full support iff the explicit finite \(S_n(\epsilon)\succeq0\) | PROVED_PAPER | Closed-form Riesz inverse on the already positive tail; exact Schur identity | The matrix \(\left(\begin{smallmatrix}1&2\\2&1\end{smallmatrix}\right)\) defeats diagonal-only checks | ABSTRACT / PAPER, new |
| R8 | \(S_n(1/n)\succeq0\) for every integer \(n\ge1\) | OPEN_NO_MECHANISM | Candidate: source-faithful residual lower certificates (C20), with one proved rule in n; that rule is missing | A certified negative upper witness at one n refutes this target; finite passing samples do not prove it | COFINAL_FAMILY / CONDITIONAL |
| R9 | R8 implies \(Q(f)\ge0\) for every compact smooth f | PROVED_PAPER | Fix f, apply (C21) for arbitrarily large n; the error \(1/n\) vanishes | A schedule covering only some shapes, or an error not tending to zero for the fixed test, fails | COFINAL_FAMILY / PAPER, conditional implication |
| R10 | Full compact-test Weil nonnegativity implies RH | PROVED_PAPER | Published criterion CC20, with (C1)'s convention | Wrong test ideal or wrong sign is not the cited criterion | ABSTRACT / PAPER, published implication |

R8 is a **target**, not a granted premise masquerading as an existing theorem. Therefore this is an IRREDUCIBLE_ATOM answer, not FULL_CHAIN. Equivalence of a target with the ultimate conclusion does not prohibit attempting it; it does prohibit claiming a proof after assuming it. BP explicitly makes this distinction. No impossibility of a different representation is claimed.

## 2. Q1(a): the first break is a mean direction, not a large prime count

### 2.1 Exact three-lobe witness against P1's small-mean step

Let \(a=\log2\), \(b=\log3\), \(\delta=(b-a)/8\), and take centers \(0,a,b\). For common even profile \(\eta\), the two total moment equations on \(\sum z_i U_{x_i}\eta\) reduce to
\[
 V_3z=0,\qquad
 V_3=\begin{pmatrix}1&\sqrt2&\sqrt3\\1&1/\sqrt2&1/\sqrt3\end{pmatrix}.
\]
The exact vector
\[
 \boxed{z=(-1,2\sqrt2,-\sqrt3)^t,\qquad V_3z=0,\quad\|z\|^2=12} \tag{C2}
\]
is the lost mean direction. There is no small singular value to invert on it: it is a true kernel.

To make the falsifier completely admissible, choose a nonnegative even smooth mollifier \(\rho\), of integral one, supported in \((-\delta/4,\delta/4)\), and set
\(\eta=1_{[-\delta/2,\delta/2]}*\rho\).
Then \(\eta\in C_c^\infty(I)\), \(0\le\eta\le1\), and
\(\int\eta=\delta\), \(\|\eta\|^2\le\delta\). Set \(h_i=z_i\eta\). Both total pole moments vanish exactly. Nevertheless
\[
 \boxed{\frac{\sum_i|\int h_i|^2}{\sum_i\|h_i\|^2}
 =\frac{\delta^2}{\|\eta\|^2}\ge\delta>\frac d{25},
 \qquad d=13/125.} \tag{C3}
\]
Here \(\delta>1/20\) follows from \(\log(3/2)>2/5\), whereas \(d/25=13/3125<1/20\). This contradicts the **copied** estimate P (P17), not Theorem P1 on its original two-lobe domain. [ABSTRACT][PAPER]

The first specified enlargement is thus already the break of that rope. After centering, its outer radius is
\[
 R_3=\frac{b+2\delta}{2}=\frac{5\log3-\log2}{8}. \tag{C4}
\]
No claim is made that this is a universal critical radius for Weil positivity, or for every conceivable direct-energy estimate. There is no unique first radius before a precise enlargement and a precise sufficient estimate are fixed.

### 2.2 The straightforward scalar rescue also fails on this cell

For separated profiles supported in intervals of width at most d, put
\[
 b_0(d)=2dA(d)+2\int_d^\infty A-c_A,\qquad
 J(s,d)=\int_{s-d}^{s+d}A(t)dt.
\]
P's energy argument gives
\[
 Q(v)\ge b_0(d)H-A(d)\|m\|^2-u^t\Gamma u,
 \quad u_i=\|h_i\|,\quad H=\|u\|^2, \tag{C5}
\]
where the nonnegative symmetric matrix \(\Gamma\) has off-diagonal entries \(J(|x_i-x_j|,d)\) plus the corresponding prime-atom weights. For centers \(0,a,b\), only 2 and 3 occur; the entry at b-a has no prime atom but retains its archimedean contribution.

Using the valid trivial estimate \(\|m\|^2\le dH\) produces
\[
 B_3(d)=dA(d)+2\int_d^\infty A-c_A-\lambda_{\max}(\Gamma)<0
 \quad(d=13/125). \tag{C6}
\]
Here is a proof of the strict sign, without a numerical run. P (P21) gives \(dA(d)<3/5\). With \(y=e^{-d/2}\),
\[
 2\int_d^\infty A=\log\coth(d/4)+2\arctan y.
\]
Since \(\coth(d/4)\le1+4/d\), \(\pi>3\), and
\(\log(171/104)<1/2\), one has
\(\log\coth(d/4)-\log(8\pi)<1/2\).
The logarithm inequality follows from
\(e^{1/2}>1+1/2+1/8+1/48=79/48>171/104\).
Also \(2\arctan y<\pi/2\), and \(\gamma_E>1/2\). For the latter elementary bound, use
\(\gamma_E>H_6-\log7\), \(H_6=49/20\), and \(e^{39/20}>7\), already from its first eight positive Taylor terms. Hence \(2\int_d^\infty A-c_A<0\).

Finally \(\lambda_{\max}(\Gamma)\) is at least the largest eigenvalue of the nonnegative prime star with edge weights \(w_2,w_3\), namely \(\sqrt{w_2^2+w_3^2}>3/5\). Use \(w_2>4/9\), \(w_3>4/7\); these follow from \(\log2>2/3\), \(\log3>1\), \(\sqrt2<3/2\), \(\sqrt3<7/4\). The variational comparison uses the nonnegative Perron vector of that star. This proves (C6).

**Precisely what is negative:** a sufficient scalar lower-budget coefficient. The actual value Q(v) is not bounded above by (C6). Therefore (C6) cannot refute three-lobe positivity. The repair is to retain the mean direction (C2), its signed prime/archimedean energy, and its coupling to the other profiles instead of charging every term at its worst absolute value.

For illustration, on the normalized mean vector z, the prime-only matrix contributes
\[
 \frac{-2w_2z_0z_1-2w_3z_0z_2}{\|z\|^2}
 =\frac{\log(4/3)}6>0. \tag{C7}
\]
Thus the newly free mean direction is not automatically a negative prime direction. This exact cancellation is destroyed by the scalar rescue. It does not prove the full mean/coupling block positive.

### 2.3 What happens at large radius

The prime sum eventually defeats absolute-value budgets, but is not the first failure above. For a single interval of length L=2R, a universal elementary bound is
\[
 \mathcal D(f)\ge\left[L A(L)+2\int_L^\infty A\right]\|f\|^2,
\]
so on the total-pole-null space the crude full bracket is
\[
 B_{\rm gross}(R)=2R A(2R)+2\int_{2R}^\infty A-c_A
       -2\sum_{n\le e^{2R}}w_n. \tag{C8}
\]
It tends to minus infinity. Partial summation and the unconditional prime number theorem give \(\sum_{n\le e^{2R}}w_n\sim2e^R\), not a theorem about the sign of each actual prime pairing. The first two terms of (C8) tend to zero. A growing bound for an operator's possible negative contribution does not prove that contribution is attained on admissible tests. [ABSTRACT][PAPER; PNT input identified]

There is a separate exact failure of archimedean-only domination even **within the pole-null class**. Fix nonzero \(g\in C_c^\infty((-1,1))\), put \(g_R(x)=R^{-1/2}g(x/R)\), and
\[
 h_R=(\partial_x^2-1/4)g_R.
\]
Both pole moments vanish by integration by parts. The shift inequality yields
\[
 \mathcal D(f)\le J_A\|f'\|^2,
 \quad J_A=2\sum_{j\ge0}(2j+1/2)^{-3}<18.
\]
Moreover \(\|h_R\|\to\|g\|/4\) and \(\|h_R'\|=O_g(R^{-1})\). Consequently
\[
 \boxed{\mathcal D(h_R)/\|h_R\|^2=O_g(R^{-2}),\qquad
 [\mathcal D(h_R)-c_A\|h_R\|^2]/\|h_R\|^2\to-c_A<0.} \tag{C9}
\]
For an explicit upper constant when R>=1 and \(R^2\ge8\|g''\|/\|g\|\), use
\(1152(\|g'\|/4+\|g'''\|)^2/(R^2\|g\|^2)\).
This is a negative upper envelope for the **archimedean-only form**, not for (C1). The prime correlations and their cancellations cannot be discarded. There is no single scale law saying that the P1 floor is always a Poincare constant proportional to R^{-2}; (C9) is a particular broad-family upper estimate, while small-support floors have logarithmic behavior.

## 3. Q1(b): what replaces the failed scalar budget

I select the **complete geometric Weil form, with its signed low-energy block**, not the stronger universal minorant Q>=n_S. This selection has a substantive advantage: all primes and poles are already explicit in (C1), and its high-frequency tail can be made positive for every fixed support without any semilocal near-resonance computation. What remains difficult is the signed low-energy comparison, not the existence of a source operator.

This is not a claim that a new global sign mechanism has been found. The exact reduction in Sections 4--5 scales as an identity and a tail theorem; its universal head sign does not yet scale as a proof. The alternative reservoir reduction remains permissible only with its entire margin and pole terms retained.

Three distinctions prevent a false chain:

* **C1 is a stronger result on a smaller class.** It is not necessary for full Q positivity; P1 already proves a larger restricted Q class without it.
* **A finite-prime Sonin projector is positive, but Q need not dominate it.** The fixed-S global minorant has already failed in the parent lineage. Varying S with support avoids that literal fixed-S counterexample, but supplies no new sign theorem automatically.
* **Convergent all-resonance kernels are a source representation, not a sign.** P (P32)--(P34) preserves the terms; it does not establish their signed comparison. No return to that representation is forced merely by (C6).

The shelf's statement that only an identity, never an inequality with slack, can reach a critical result is too strong. Bounds \(Q|_{\mathcal D_n}\ge c_n I\) with \(c_n>0\), \(c_n\downarrow0\), would suffice. So would the weaker errors in (C21). An exact global uniform gap is not required. This corrects the diagnosis without assuming any such bounds.

## 4. A new explicit tail theorem for every full support

This section supplies R6 rather than putting it into an unnamed hypothesis. The constants are intentionally wasteful. [ABSTRACT][PAPER]

### 4.1 Archimedean monotonicity from the digamma series

Let
\[
 q(\xi)=\Re\psi(1/4+i\xi/2)-\log\pi.
\]
Then \(q(0)=-c_A\), \(q\) increases with \(|\xi|\), and
\[
 q(\xi)+c_A
 =\sum_{j\ge0}\frac{(\xi/2)^2}
 {(j+1/4)((j+1/4)^2+(\xi/2)^2)}. \tag{C10}
\]
These follow by taking real parts of the convergent digamma difference series (DLMF 5.7.6). Every summand is increasing in \(|\xi|\). For T>=2, retain the indices j+1/4<=T/2, on which the summand is at least \(1/[2(j+1/4)]\). Comparing that finite harmonic sum with its integral proves
\[
 \boxed{q(T)\ge\tfrac12\log(T/2)-c_A.} \tag{C11}
\]
The estimate is very weak but explicit, unconditional, and sufficient here.

### 4.2 Fixed finite head and its orthogonal complement

For each integer n>=1 define, before any sign test,
\[
 W_n=\sum_{2\le k\le e^{2n}}w_k,\quad C_n=c_A+2W_n+1,
 \quad K_n=\lceil2e^{4C_n}\rceil,
\]
\[
 m_n=\lceil4nK_n\rceil,\qquad h_n=2n/m_n\le1/(2K_n). \tag{C12}
\]
Partition [-n,n] into m_n equal cells J_i. All these are finite explicit objects. A ceiling in the active-prime upper budget may be used provided zero correlations beyond the true support boundary are retained as zero in (C1).

In \(H_n=L^2((-n,n);\mathbb C)\), let
\[
 V_n=\operatorname{span}\{1_{J_i}:1\le i\le m_n\}
       +\operatorname{span}\{e^{x/2},e^{-x/2}\},\qquad T_n=V_n^\perp. \tag{C13}
\]
The exponentials are restricted to (-n,n) and zero-extended. Thus every y in T_n has zero mean on each cell and both total pole moments zero. The two exponentials are not omitted from the full test space: they remain in V_n, with their complete signed pole form.

Let P_K denote the full-line Fourier projection onto |xi|<=K. For y in T_n, duality against a band-limited g and the elementary interval mean inequality give
\[
 |\langle y,g\rangle|
 =\left|\sum_i\int_{J_i}\overline y(g-g_{J_i})\right|
 \le h_n\|y\|\|g'\|\le h_nK_n\|y\|\|g\|.
\]
For completeness, \(\|g-g_J\|_{L^2(J)}\le |J|\|g'\|_{L^2(J)}\) follows by averaging \(g(x)-g(z)=\int_z^x g'\), applying Cauchy--Schwarz and integrating. Therefore
\[
 \|P_{K_n}y\|^2\le\tfrac14\|y\|^2. \tag{C14}
\]
No assumption of high Fourier support is imposed on y. The estimate proves the necessary leakage control from explicit spatial constraints.

### 4.3 The tail is positive with a full prime budget

The archimedean form equals \((2\pi)^{-1}\int q|\widehat y|^2\). Use (C10)--(C14), \(|C_y(t)|\le\|y\|^2\), and the zero pole moments. Since \(q(K_n)\ge2C_n-c_A\),
\[
\begin{aligned}
 Q(y)&\ge\left[\tfrac34q(K_n)-\tfrac14c_A-2W_n\right]\|y\|^2\\
 &\ge\left[\tfrac12c_A+W_n+\tfrac32\right]\|y\|^2
 >\|y\|^2.
\end{aligned} \tag{C15}
\]
All active prime powers are paid, not just distinct primes. This holds on the tail's logarithmic-energy form domain.

### 4.4 Domains and practical limitations

The form domain consists of supported L2 functions with
\(\int\log(2+|\xi|)|\widehat f(\xi)|^2d\xi<\infty\).
The archimedean form is closed and lower bounded there; the prime shifts and the two-pole operator are bounded on each fixed support. Piecewise constants and the restricted exponentials belong to the operator domain: their Fourier transforms are O(1/|xi|), and multiplication by log(2+|xi|) still gives an L2 transform. Thus the head-to-tail cross functionals in the next section are genuine bounded L2 functionals, not formal boundary distributions.

Compact smooth functions in the open interval form a core. One proof first compresses support slightly by dilation, which is strongly continuous in the logarithmic Fourier norm, and then convolves with a smooth approximate identity small enough to preserve the support. Fourier domination and density prove convergence in that norm. This justifies using the closed form for head/tail identities and then returning to the requested smooth class.

**Do not implement (C12) as the next experiment.** Its doubly severe prime-dependent size is an existence bound demonstrating a finite obstruction at each support. A useful implementation must sharpen the tail theorem substantially. This construction is not the missing efficient or uniform sign theorem.

## 5. Q1(c,d): exact signed head, the sole remaining global target, and the quantifier

### 5.1 The head is finite; its sign is not automatic

Choose the explicit cell/exponential basis of V_n, with exact physical Gram matrix G_n, and write the full form relative to V_n plus T_n as
\[
 Q=\begin{pmatrix}A_n&E_n^*\\E_n&B_n\end{pmatrix},\qquad B_n\ge I.
\]
Here A_n is **the full form**, including poles, on the stated head. E_n is its true cross map. B_n is the closed tail form/operator from (C15). Its inverse is legitimate by that proved coercivity, not by an assumed positivity of Q.

For epsilon>0 define
\[
 \boxed{S_n(\epsilon)=A_n+\epsilon G_n
                 -E_n^*(B_n+\epsilon I)^{-1}E_n.} \tag{C16}
\]
Write v_z for the function synthesized from a head coefficient vector z. Completion of the square gives, for z and a tail y,
\[
 Q(v_z+y)+\epsilon\|v_z+y\|^2
 =z^*S_n(\epsilon)z+
 \|(B_n+\epsilon I)^{1/2}[y+(B_n+\epsilon I)^{-1}E_nz]\|^2. \tag{C17}
\]
The coordinate norm in the first component is z*G_nz. All cross pairings and the tail are included. Equation (C17) proves R7, in both directions, by minimizing over y.

**Mandatory exact detector:** for A=B=1 and E=2, the original matrix has two positive diagonal blocks but S(0)=-3. The vector (1,-1) gives full form -2. Any proposed general gluing rule certifying this example is invalid before arithmetic is considered. Positivity of C1/C2-type diagonal pieces cannot by itself pay their new mixed entries. [FINITE_CELL][PAPER]

### 5.2 A one-sided source representation for checking a head

For any explicit finite-range approximate solve Y_n into the true tail, put
\[
 Z_n=E_n+(B_n+\epsilon I)Y_n,
\]
\[
 C_n^Y=A_n+\epsilon G_n+E_n^*Y_n+Y_n^*E_n
                    +Y_n^*(B_n+\epsilon I)Y_n.
\]
Direct expansion proves
\[
 S_n(\epsilon)=C_n^Y-Z_n^*(B_n+\epsilon I)^{-1}Z_n, \tag{C18}
\]
so the valid lower and upper envelopes are
\[
 \boxed{C_n^Y-(1+\epsilon)^{-1}Z_n^*Z_n
       \preceq S_n(\epsilon)\preceq C_n^Y.} \tag{C19}
\]
The full residual Z_n is mandatory, including every part outside the solve space. This is the same useful algebraic principle as the residual certificates already encountered in the project; its novelty here is the full-support consumer and explicit tail (C15), not a claim to have invented Schur complementation.

An independent source-derived construction proving
\[
 C_n^{Y_n}-(1+1/n)^{-1}Z_n^*Z_n\succeq0
 \quad\hbox{for every }n \tag{C20}
\]
would supply the atom. No such Y_n-family and no sign proof of (C20) are on the pinned shelf. A different signed certificate for (C16) is allowed; (C20) is sufficient, not made necessary by its name.

### 5.3 The atom, stated without a disguised conclusion

**ALL_SUPPORT_SIGNED_SCHUR_HEAD_LOWER_BOUND:** for the explicit objects (C10)--(C16), prove \(S_n(1/n)\succeq0\) for every integer n>=1, from the geometric coefficients of (C1), not from assumed Weil positivity or facts about zero locations.

This is an exact remaining source inequality. It is not claimed to be strictly weaker than the terminal assertion, nor to be new merely because it has finite-dimensional coordinates. It is called the irreducible atom **relative to the present dependency ledger**: all surrounding steps above and below are proved, while this universal sign lacks a source-specific proof mechanism. An absolute theorem that no further representation can simplify it is neither known nor asserted.

This is also the answer to “what makes the chain finite?” A finite proof of a theorem quantified over n would do so. A source-defined induction invariant, an all-n factorization, or a uniform residual construction such as (C20) could provide that finite proof. **None has been supplied.** Merely naming S_n or computing an indefinitely growing list of positive heads is not that structure. This is the missing part, not a promise hidden after the last table row.

### 5.4 The terminal passage needs no uniform positive gap

If the atom were proved, (C17) would give
\[
 Q(f)\ge-\frac1n\|f\|^2\qquad(f\in\mathcal D_n). \tag{C21}
\]
Fix any f in C_c^infinity(R). For every sufficiently large integer n it belongs to D_n, and Q(f) is the **same number** in each restriction: all subsequently added prime terms have zero autocorrelation on that fixed support. Let n tend to infinity in (C21). Then Q(f)>=0. This proves R9 with no norm limit of f, no evolving normalization, and no assumed spectral monotonicity.

Alternatively, exact positivity on every D_n suffices simply by their union; its constants may depend arbitrarily badly on n. The infimum of the spectral bottom is nonincreasing under support enlargement, so positivity of one small window does not propagate to larger windows in the desired direction. No monotonicity shortcut supplies R8.

CC20 also states a published criterion with finitely many imposed Mellin zeros. That can legitimately remove pole directions in a different terminal interface, after the precise convention is checked. Here the request fixes the full all-test form, so (C13)--(C17) keep the pole directions in the finite head. They are not silently discarded.

### 5.5 What a bounded computation can and cannot decide

A certified upper value \(Q(f)<0\) for a literal compact test refutes global positivity and hence the atom: choose n large enough that \(\|f\|^2/n<-Q(f)\). More specifically an upper head witness \(z^*C_n^Yz<0\) refutes the corresponding shifted-head assertion. A lower envelope in (C19) that is negative or straddles zero refutes neither.

No finite set of successful windows decides the universal atom. The proposed bounded diagnostic in Section 8 is decisive about the **first attempted transfer mechanism** and can falsify the atom if it yields a genuine negative Q witness. Its positive outcome is deliberately not sold as a decision that the atom is true.

## 6. Q2: the first three requested ropes, without pretending they are three successive successes

### R_next1: three independent lobes

The candidate theorem is
\[
 Q\left(h_0+U_a h_1+U_b h_2\right)
 \ge\frac1{100}\sum_{i=0}^2\|h_i\|^2, \tag{C22}
\]
for the same I and the two **total** pole equations. It is an explicit conjectured local target, not proved here. Even the weaker zero right-hand side is not established here. Translation to the centered support changes neither Q nor the vanishing of its two moments.

The correct budget must preserve (C2). In exact finite-head/tail coordinates on this three-support space, a sufficient rational bracket for (C22) is
\[
 A_3-\tfrac1{100}G_3+E_3^*Y+Y^*E_3+Y^*(B_3-\tfrac1{100}I)Y
 -\tfrac{100}{99}Z^*Z\succeq0,
\quad Z=E_3+(B_3-\tfrac1{100}I)Y, \tag{C23}
\]
provided B_3>=I has first been proved for that declared split. Section 4 supplies an existence version of such a split by partitioning each of the three intervals, using W=w_2+w_3 and total moments in the head; sharper local bounds should replace its huge cutoff for implementation.

This is a real signed matrix budget, not a claimed certificate. The scalar budget (C6) does not work. The one-dimensional center-mean kernel is only the first newly free direction; arbitrary profile shapes and their coupling are still infinite-dimensional until a tail bound is supplied.

**Cost / kill-power:** 2/10 / 9/10 for the seven-dimensional diagnostic below; substantially higher for an actual whole-class residual certificate. **Falsifier:** the source total-pole-null z-mean sector together with independent mean-null variations, not only a common positive bump. A negative upper Q witness kills the zero-floor theorem; a value below 1/100 alone kills only its strengthened constant.

### R_next2: the first failure and its repair are on that same cell

There is not a second known later radius to quote. The first failed proof rope is (P17) on the very three-lobe extension requested in R_next1. Equation (C3) closes this diagnosis now, before any computation. Its replacement is a signed estimate on the unremoved mean/coupling block, such as (C23). No new list of primes or analytic limit is needed to expose it.

**Cost / kill-power:** 1/10 / 10/10 for the completed algebraic diagnosis; 5/10 / 9/10 as an ordinal estimate for a useful local signed repair after domain control. The latter is not a runtime promise. **Falsifier:** a purported estimate \(\|m\|^2\le(d/25)H\) must reject (C3); a block-sign rule must reject the 2-by-2 gluing plant.

### R_next3: the first two-prime near-resonance question

This is an alternative representation of the same three-center class, not a necessary extra rope after its direct Q sign. P Lemma P2 extracts every source log-ratio resonance, including those lying inside the seven lag neighborhoods. It proves local L1 convergence of the extracted part and W1,1 convergence of the remainder; it does not prove P (P34)'s sign.

For a fixed prime set of size s, the analogous elementary counting bound has at most O_S((N+1)^s) frequencies below e^N and O_S((N+1)^{2s}) pairs. The L1 and W1,1 tails are controlled by sums of the forms
\[
 C_S\sum_{N\ge M}(N+1)^{2s+1}e^{-N},\qquad
 C'_S\sum_{N\ge M}(N+1)^{2s}e^{-N/2}. \tag{C24}
\]
These are convergence estimates for **fixed S**. They give no uniform sign as S grows with support; their constants and exponents cannot be copied unchanged.

**First missing estimate:** the signed compressed all-resonance principal part plus its actual remainder must be nonnegative on the total-moment-null joint class, with all mixed entries, or its negative part must be bounded by a retained positive source contribution. That estimate is not supplied by (C24).

**Cost / kill-power:** 8/10 / 10/10 for a faithful signed source comparison. **Falsifier:** choose distinct ratios of 2^j3^k arbitrarily close to one; any proof using a universal nonresonant separation kappa is wrong. A negative principal piece alone still does not refute the complete form.

## 7. Q3: stop list, and Q4: publication cut

### 7.1 Stop treating these activities as gates to the chosen chain

| Activity | Decision | Exact reason |
|---|---|---|
| Plus-channel full-margin sign | Stop as a terminal-chain gate; retain as a separate scientific question | Q, not Q-n_2, is the consumer. The withdrawn J-table does not determine the sign. |
| Euler--Gram evaluator | Pause as the main route to the direct three-lobe Q question; retain for reservoir science and a source cross-check | Equation (C1) already computes Q without subtracting two large traces. |
| More unstructured positive packets | Stop | They supply no all-support induction and often omit the newly free mean/coupling direction. |
| Further scalar-floor sharpening inside the already closed minus cell | Stop as global progress | A larger lower number there does not create missing joint tests elsewhere. |
| Independent source/certificate review for C1 and P1 | Continue | It establishes what can legitimately enter the paper and the ledger; one successful hash is not that review. |
| Explicit joint low-mean/coupling test with source Gram and total moments | On the selected local branch | It is aimed at the first actual failed transfer, with a frozen object and a negative-witness criterion. |
| Search for an all-n signed-head invariant / source positive representation | Main research obligation | This, not adding more windows, is what could replace R8 by a proved rope. |
| Two-prime kernel work without a proposed signed comparison | Stop as a closure claim; retain only a bounded identity audit | Convergence is already distinguished from sign in P2. |

No successful diagnostic is allowed to restart the old loop “new packet, new cutoff, same unproved universal comparison.” The supplied shelf does not establish that the next broad source sign is impossible; it establishes that the current successful cells do not imply it.

### 7.2 First self-contained publication unit

The strongest first unit is **C1 as the central theorem, with C2 as a separate elementary extension/comparison**, after their exact source identities and certificate implementation are independently audited. The two-prime extraction lemma is optional background or a later paper; its unresolved sign is not required to state or prove C1.

A defensible title claim is: **“A pole-gauged Fourier certificate for a prime-2 Weil--Sonin inequality on a fixed moment-null class.”**

The main statement is G's exact source-square identity and half-principal lower bound on its fixed H00(I) minus class. P1 may then state Q>=||v||^2/100 for two independent profiles with only total pole moments zero. These are different strengths and domains and must be printed separately. The fixed prime atom, cutoff, intervals, Fourier normalization, PAPER identities, ARB norm certificate, source code and archived outward endpoints must be explicit.

The honest scope sentence is: **“The results prove restricted inequalities on specified fixed supports, not an exhausting family, and make no conclusion about the zeros of the Riemann zeta function.”** No first-in-the-world, priority, or journal-acceptance claim has been established by this audit. New results in the present CHAIN document are PAPER derivations pending independent review; they are not automatically added to that publication's proved dependency list.

## 8. Predictions, the single proposed check, and the dependency closeout

### 8.1 Frozen observer forecasts

| Prediction | Frozen p | Fate | Reason |
|---|---:|---|---|
| P_BREAK_IS_PRIME_SUM | 0.55 | REFUTED_FOR_THE_FIRST_LITERAL_P1_EXTENSION | The exact three-center mean nullspace already breaks (P17). Prime growth remains a later obstacle to absolute budgets, not the first one. |
| P_REPLACEMENT_IS_RESERVOIR_MINORANT | 0.45 | REFUTED_AS_ROUTE_SELECTION | The selected determining object is the full geometric signed head, not the stronger Q>=n_S minorant. |
| P_CHAIN_HAS_FINITE_STRUCTURE_NAMED | 0.35 | NOT_DELIVERED_AS_A_GLOBAL_SIGN_STRUCTURE | A finite head per support and a finite dependency schema are given. No verified all-support induction/invariant is named as an existing sign mechanism; that distinction is the atom, not a scoreable success. |
| P_ATOM_NAMED_WITH_TEST | 0.60 | CONFIRMED_WITH_FALSIFICATION_SCOPE_ONLY | (C16), R8, and Section 8.4 define the atom and an explicit bounded falsifier. A finite positive run cannot decide the universal truth. |
| P_STOP_LIST_INCLUDES_MARGIN_SIGN | 0.70 | CONFIRMED | Section 7 removes the optional full-margin sign from the critical path. |

The source question is not refuted merely because a proof-output forecast failed. No frozen probability or old artifact is edited.

### 8.2 Original PROFILES registrations

| Original event | p | Fate in this intake |
|---|---:|---|
| P_PROFILES_DIRECT_TOTAL_MOMENT_WEIL_FLOOR_SURVIVES | 0.88 | PENDING_INDEPENDENT_AUDIT. P17--P26 were rechecked here without a new defect; this is a self-review by their author, not the separate audit event. |
| P_PROFILES_LOG_PRINCIPAL_RESERVOIR_ORDER_SURVIVES | 0.96 | RETAINED_PAPER; independent event not closed by this document. The digamma order is consistent with (C10)--(C11). |
| P_PROFILES_D1_PROFILE_VERSUS_PHYSICAL_GAUGE_CHECK_SURVIVES | 0.95 | RETAINED_PAPER; no new independent receipt supplied. It is not used to prove the new tail or chain. |
| P_PROFILES_ALL_RESONANCE_LOCAL_EXTRACTION_SURVIVES | 0.84 | RETAINED_PAPER; independent event pending. No sign or uniform-in-S result added by the fixed-S convergence proof. |

REQ explicitly says the P1 audit is running. No later result was looked up or inferred from branch movement to close these events.

### 8.3 This intake's registrations

Before the new tests, the living chat registered a three-lobe mean-control obstruction at 0.85 and absence of a shelf-closed global chain at 0.80. The first has the exact self-derived witness (C2)--(C3). The second is supported at the declared shelf boundary: the source-specific universal sign rule is not among its suppliers. These are self-scored intake outcomes, not independent confirmations or probabilities about RH.

Prospective events for the next independent check, registered now before that check:
```yaml
P_CHAIN_THREE_LOBE_MEAN_FALSIFIER_SURVIVES:
  probability: 0.98
  event: independent_review_accepts_C2_C3_and_the_scope_of_C6
  fate: PENDING
P_CHAIN_EXPLICIT_FULL_SUPPORT_TAIL_SURVIVES:
  probability: 0.90
  event: independent_review_accepts_C10_through_C19_including_the_form_domain
  fate: PENDING
P_CHAIN_FROZEN_SEVEN_DIMENSIONAL_THREE_LOBE_FLOOR:
  probability: 0.65
  event: the_exact_packet_in_section_8_4_has_certified_generalized_lower_eigenvalue_at_least_1_over_100
  fate: PENDING
```
These do not authorize a change of profile, class, cutoff or normalization after seeing results.

### 8.4 One CODEX DIRECTIVE: CHAIN_SIGNED_NULL_MEAN_TRANSFER_PREFLIGHT

This is a **proposed next bounded check**, not a numerical run performed by this adjudication.

First independently check the exact mean null vector and the copied-budget failure (C2)--(C6). Then, only for this declared three-lobe diagnostic, set
\[
 \eta(x)=\begin{cases}\exp[-1/(1-(2x/\delta)^2)],&|x|<\delta/2,\\0,&|x|\ge\delta/2,\end{cases}
\]
\[
 \phi_0=\eta,\quad \phi_1=\eta',\quad \phi_2=\eta''-\eta/4,
 \qquad f_{ij}=U_{x_i}\phi_j,
 \quad x_i\in\{0,\log2,\log3\}. \tag{C25}
\]
Use all nine generators, their exact Gram, and both total pole rows. Because eta is even,
\(M_+(\eta)=M_-(\eta)=m_\eta>0\) and
\[
 M_\pm(\phi_0)=m_\eta,\quad
 M_\pm(\phi_1)=\mp m_\eta/2,\quad M_\pm(\phi_2)=0.
\]
After removing the common nonzero factor, the two total-moment rows have algebraic entries \(e^{\pm x_i/2}(1,\mp1/2,0)\). Their exact rank is two. Work in their seven-dimensional kernel, not a floating-point projection. The physical Gram must still be proved positive in those coordinates; neither the row rank nor the number of generators substitutes for that check.

Assemble the complete polarized form from (C1), with all archimedean self and cross pairings, the atoms at log2 and log3, and the pole term before exact restriction. Include the vector \((-1,2\sqrt2,-\sqrt3)\otimes(1,0,0)\) and its couplings to the other six directions. The lag b-a has an archimedean cross entry and no prime atom. No Sonin table, residual difference of large traces, or fitted normalization is allowed. The coverage ledger must include the six support endpoints x_i plus or minus delta/2, all correlation endpoints x_i-x_j plus or minus delta, the archimedean contact at zero, both active prime shifts, and every quadrature tail. Integrate the cancelled archimedean expression at zero, not its divergent pieces separately.

Return lower/upper Hermitian envelopes with a proved generalized error at most 1/1000 in the exact Gram norm, or identify the failed error supplier. A lower eigenvalue >=1/100 verifies only the registered packet event. An upper negative Q value on a normalized exact witness is decisive against the source sign. A failure of Q>=||v||^2/100 without Q<0 refutes only the stronger local floor. Straddling zero is inconclusive and must identify the dominant error.

**No automatic enlargement after this packet.** A positive packet must be accompanied by a candidate signed mean/complement inequality capable of covering the omitted profiles, or the activity stops as finite evidence. It does not discharge R8. The conservative universal mesh (C12) is expressly not a requested run.

Success report: exact Gram and pole rows, seven-dimensional source envelopes, retained mean direction, error ledger, and the first viable whole-class inequality. Failure report: `CHAIN_MEAN_OR_MIXED_SOURCE_BOUND_UNRESOLVED`, or `CHAIN_LITERAL_NEGATIVE_UPPER_WITNESS` with the exact test and upper enclosure. The deliberately false 2-by-2 gluing matrix must be rejected by the same envelope logic before any positive result is credited.

### 8.5 Two representations, consumer contract, and strongest attack

| Representation | Determining object | Power / cost, ordinal | Main risk |
|---|---|---|---|
| Full geometric low-mean / signed Schur head | (C16), with full poles and all active primes | 10/10 / 3/10 for local preflight; global cost unknown | No source-specific all-n sign invariant; conservative tail has impractical dimension |
| Source reservoir plus the complete signed remainder | Euler--Gram source with Q=n_S+margin+pole, all joint profiles | 9/10 / 8/10 for a larger fixed-S comparison | Stronger-than-needed minorant, nonuniform prime-set constants, or omitted mixed/pole terms |

Both preserve the actual source and terminal quantifier. Neither is a proof of the global sign on the current shelf.

**Strongest attack:** “You have only moved the original unknown into S_n.” For the universal sign this objection is correct. What has been proved is the explicit tail, the finite signed reduction, the exact first failed mean estimate, and the terminal quantifier passage. What has **not** been proved is a sign-generating mechanism for S_n. This is why the result is IRREDUCIBLE_ATOM, not an advertised global route completion. The exact residual envelopes make a proposed mechanism testable; they do not manufacture it.

**K8A.** DOWNSTREAM_CONSUMER: the published criterion on all complex compact smooth tests in the frozen convention. ACTUAL_CONSUMER_REQUIREMENT: nonnegativity of (C1) on that full class. ORIGINAL_REQUESTED_OBJECT: a finite proof chain from the restricted C1/C2 cells to that assertion. ORIGINAL_OBJECT_IS: NOT_NECESSARY for C1/C2 themselves; neither their reservoir improvement nor this particular Schur representation is necessary for the terminal sign. KNOWN_WEAKER_INTERFACES: source-valid errors tending to zero as in (C21); exact positivity on every exhausting full space without a uniform positive constant; the published finite-Mellin-constraint criterion after its own crosswalk. Each is an implication, not an assumed supplier.

FAILURE_TYPE: COUNTEREXAMPLE for the copied three-lobe mean bound and archimedean-only broad pole-null positivity; NO_DERIVATION for the universal signed-head bound; OTHER for the missing cited GAP file. EPISTEMIC_STATUS: the exact failed theorem shapes are MATHEMATICALLY_DEAD at their specified scope; global sign and local three-lobe repair remain RESEARCH_DEBT. KILL_SCOPE is THEOREM_SHAPE only. Evidence: (C3), and the strict negative archimedean upper envelope (C9). The negative sufficient bracket (C6) is not classified as a negative source witness.

NOVELTY_AXIS: retaining the first free mean direction and separating a universally available positive high tail from a genuinely unknown joint low-energy sign. Historical priority is not claimed. REOPEN_TRIGGER for the atom: an actual source-defined all-n sign construction, or a certified negative upper source witness. REOPEN_TRIGGER for local three-lobe debt: a valid bound such as (C23) with its complete complement, or a literal counterexample. REOPEN_TRIGGER for a reservoir alternative: a cancellation-preserving source estimate with its growing-S and support dependence, not repetition of fixed-S convergence.

```yaml
META_CLOSEOUT:
  PROGRESS_CLASS: REPRESENTATION_PROGRESS
  COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
  ROUTE_SCORE: 4
  WHAT_BECAME_SMALLER:
    - first_failed_P1_rope_is_an_exact_three_lobe_mean_direction
    - every_full_support_has_an_explicit_positive_tail
    - all_remaining_global_sign_debt_is_in_the_source_signed_heads
    - terminal_passage_needs_only_one_over_n_lower_error_not_a_uniform_gap
  WHAT_WAS_REFUTED:
    - copied_two_moment_small_mean_bound_for_three_lobes
    - archimedean_only_domination_on_all_broad_pole_null_tests
    - diagonal_positive_cells_as_a_sufficient_gluing_rule
  WHAT_WAS_NOT_PROVED:
    - three_lobe_whole_class_positive_floor
    - universal_signed_head_bound
    - a_finite_source_specific_sign_induction
    - RH
  MUST_NOT_RECUR:
    - call_a_finite_head_per_window_a_finite_proof_for_all_windows
    - infer_a_negative_Weil_direction_from_a_negative_sufficient_budget
    - remove_the_kernel_of_the_center_moment_matrix
    - treat_a_reservoir_as_a_minorant_without_its_signed_remainder
    - treat_self_review_or_matching_hashes_as_an_independent_proof_gate
  MEMORY:
    target: REQ-2026-09-07-CHAIN
    status: OPEN
    invariant: full_joint_source_forms_and_all_support_quantifiers_survive_every_reduction
    remaining_unknown: ALL_SUPPORT_SIGNED_SCHUR_HEAD_LOWER_BOUND
    next_decisive_test: frozen_three_lobe_seven_dimensional_mean_and_coupling_preflight
PUBLICATION_HANDOFF:
  BRANCH: rh_clean
  PATHS_WRITTEN:
    - docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_FULL_CHAIN_TO_WEIL_2026-09-07.md
  LEAN_FILES_WRITTEN: []
  LEAN_GATE_COMMANDS: NOT_APPLICABLE_DOCUMENT_ONLY
  EXPECTED_AXIOM_PROFILE: NOT_APPLICABLE_NO_KERNEL_GATE
  COMMIT_AND_READBACK_BLOB: delivery_receipt
  RECEIPT_CHANGES_ONLY: publication_status
```

## 9. PROSHKA'S OWN LINE

I choose the complete Weil form because it is the actual consumer, with the primes already explicit.
The reservoir is useful structure, but insisting that Q dominate it can ask for more than the consumer needs.
The scalar floor is even narrower; its positive minus channel does not control arbitrary profile combinations.
The second nearest alternative is a growing-prime positive Fourier extension.
Its attraction is a single square; its unsolved part is precisely the signed extension, not the convergence of its series.
I have no justified basis for claiming that this alternative will automatically work at every scale.
The first move beyond this batch is to expose the three-lobe mean direction with all its mixed entries.
The exact vector in this verdict prevents the computation from looking only where the old theorem already wins.
A genuine negative upper Q witness would kill the proposed local sign.
A negative scalar budget would instead kill only that budget and would not justify abandoning the class.
The next move, after a successful local test, is to derive a signed transfer estimate for the omitted profiles.
That move dies as a closure strategy if it produces only another finite packet without a complement statement.
For the global problem I would ask for an invariant or recurrence for the signed heads, not another graph of positive eigenvalues.
One sharp source identity controlling the new coupling would matter more than many isolated positive rows.
I would ask for the exact Gram and total-moment rows of the proposed diagnostic, with its outward error ledger.
I would not ask for another retained-mode plus-channel margin table to decide direct Q positivity.
The source moment algebra surprised me: the first new kernel appears with only three lobes.
Its prime contribution is not automatically adverse; absolute-value accounting throws away a real cancellation.
That makes a local signed repair worth investigating, but it does not justify forecasting the global repair as done.
I distrust statements that turn a fixed-prime theorem into a theorem uniform in a growing prime set.
I also distrust the claim that a critical result requires a globally uniform positive gap or forbids every inequality with slack.
The exact quantifier argument shows why vanishing negative errors would already suffice.
The very large cutoff in my tail theorem is a warning about cost, not a recommended implementation.
It demonstrates where the unknown can be isolated; it does not tell us how to obtain its sign efficiently.
C1 and C2 remain real results, but they are not evidence that every later pillar is already designed.
The honest unfinished work is a source-specific global sign mechanism for the low-energy heads.
I have specified its objects, its surrounding proved implications, and the test that can expose the first bad transfer.
I have not replaced that missing proof by the words “and then all windows are positive.”

Only this verdict is to be published. The request, old verdicts, code, forecasts, queue, and route state remain unchanged. New derivations are PAPER, pending independent review. No RH claim is made.
