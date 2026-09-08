# STATUS: TRY_DIRECTIONAL_COMPENSATION_WITH_WIDTH_EVIDENCE_LOCK
```yaml
OPERATIVE_CLASS: TRY_DIRECTIONAL_COMPENSATION_WITH_WIDTH_EVIDENCE_LOCK
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-07-COMPENSATE
ADDENDUM_ID: WIDTH
BOUNDARY: SUPPLEMENTAL_EVIDENCE_INTAKE_NOT_A_NEW_FULL_ADJUDICATION
RESULT: PARTIAL_WITH_PRECISE_REMAINDER
SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  PATH: docs/routeB_bus/proshka/PROSHKA_ADDENDUM_GOAL058_COMPENSATE_WIDTH_2026-09-07.md
  COMMIT: 2c1727ec060dcfad7a1ff2bbb6fc755485a05c0d
  GIT_BLOB: b71e6551733ce2e794215afb2a7f56024ec28489
  SHA256: f10a308a48966d1cef198330e6fdfcbe5e5fea104f8c682030b0b8a9c26873f0
  BYTES: 1683
  LINES: 17
  FINAL_LF: true
  GITHUB_CONNECTOR_FETCH: true
  UTF8_SHA256_AND_GIT_BLOB_RECOMPUTED: true
  HASH_AND_LINE_CHECKS_MATCH: true
BOOTSTRAP:
  PATH: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
  REF: rh_clean
  GIT_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
PARENT_VERDICT:
  PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_COMPENSATE_2026-09-07.md
  COMMIT: 8868b50cfd96d5a9a6cabf9a62ecfccfd8a42d32
  GIT_BLOB: c1d642bff22990c4399223ba1db18213b3b71680
  SHA256: d7286b7f99c6db0a109ab7831505512c05b1e78b37be41a78c207766538d3069
  LOCAL_BYTES_MATCH_PINNED_BLOB: true
  MODIFIED: false
  RESULT_CODES_CHANGED: false
EVIDENCE:
  WIDTH_NUMBERS: DIAGNOSTIC_NEVER_A_PROOF
  NUMERICAL_SCOPE: FINITE_CELL
  NUMERICAL_VERIFIER: CONDITIONAL
  RAW_ASSEMBLY_AND_ERROR_BOUNDS_RECHECKED: false
  NEW_VARIATIONAL_AND_ALGEBRAIC_STATEMENTS:
    SCOPE: ABSTRACT
    VERIFIER: PAPER
    INDEPENDENT_REVIEW: pending
DECISIONS:
  WIDTH_ENLARGEMENT_SELECTED_AS_FLOOR_REPAIR: false
  TRUE_CLASS_BOTTOM_NONINCREASING_WITH_WIDTH: proved_by_inclusion
  REPORTED_PACKET_MINIMA_ARE_CLASS_LOWER_BOUNDS: false
  ALL_WIDTH_CURVES_TEND_TO_ZERO_FROM_ABOVE: not_established
  ALL_LOSSY_INEQUALITIES_EXCLUDED: false
  SELECTED_ALL_N_INTERFACE: parent_equation_42_directional_compensation
  EXACT_POSITIVE_SERIES_AUTOMATICALLY_GIVES_UNIFORM_FINITE_STOPPING: false
  SIX_PROFILE_FULL_CLASS_CLOSED: false
  ALL_N_SUCCESS_CRITERION_MET: false
CLOSES: []
OPENS: []
CLOSES_ANALYTIC_RH_SUPPLIERS: []
REVIEW_COMPLETED: WIDTH_SOURCE_LOCK_AND_EVIDENCE_INTERPRETATION
REMAINS_OPEN:
  - full_six_profile_signed_head_lower_bound
  - ALL_SUPPORT_SIGNED_SCHUR_HEAD_LOWER_BOUND
EXECUTION:
  HASH_COMPUTATION: true
  NUMERICAL_EXPERIMENT: false
  LEAN_EDIT: false
  ARISTOTLE: false
  SHARED_STATE_OR_QUEUE_EDIT: false
PUBLICATION:
  PATH: docs/routeB_bus/proshka/PROSHKA_SUPPLEMENT_GOAL058_COMPENSATE_WIDTH_2026-09-08.md
  BRANCH: rh_clean
  COMMIT_AND_READBACK_BLOB: delivery_receipt
  ONLY_THIS_NEW_DOCUMENT_TO_BE_WRITTEN: true
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## 1. Intake and decision

**WIDTH supports retaining directional compensation as the research target. It does not prove that every inequality with loss is impossible.** The closed COMPENSATE verdict stays unchanged. This supplement records the new data and their exact logical reach; it does not reopen the whole batch.

[W] denotes the pinned WIDTH file above, read completely through GitHub. Its fetched UTF-8 content, including final LF, matches both supplied hashes and the 17-line count after recomputation. [C] denotes the pinned parent verdict above; its available complete bytes match the pinned blob and SHA-256, and Section 6 was read back through GitHub. No raw WIDTH arrays, new numerical assembly, or outside research are used here.

[W] reports Legendre degrees below four, both total pole moments imposed, and the physical Gram including cross terms after overlap. Its reported minima are:

| Largest prime P | Fixed half-width | Square-root growth | Linear growth |
|---|---:|---:|---:|
| 11 | 0.537 | 0.240 | 0.0366 |
| 23 | 0.184 | 0.0400 | 0.0064 |
| 47 | 0.073 | 0.0069 | 0.0008 |

The schedules are `delta(P) = delta_0 (log P / log 3)^gamma`, with `gamma = 0, 1/2, 1`. These are **reported finite-packet values**, not certified infinite-class floors. [W, lines 9–13; FINITE_CELL / CONDITIONAL]

## 2. What width enlargement proves, without numerics

Fix P. Let `V(P,delta)` be the actual synthesized smooth functions

\[
 f=\sum_{p\in\{1\}\cup\{p\le P:p\text{ prime}\}}U_{\log p}h_p,
 \qquad h_p\in C_c^\infty(-\delta,\delta),\qquad M_+(f)=M_-(f)=0.
\]

Use the physical norm of f, and define

\[
 \lambda(P,\delta)=\inf_{0\ne f\in V(P,\delta)}
                    \frac{\mathcal Q(f)}{\|f\|_2^2}.
\]

**Width-inclusion lemma.** If `delta_1 <= delta_2`, then

\[
 V(P,\delta_1)\subseteq V(P,\delta_2),\qquad
 \lambda(P,\delta_2)\le\lambda(P,\delta_1).                 \tag{W1}
\]

Every old profile remains admissible, its synthesized function and total moments remain unchanged, and the infimum is now taken over a larger set. This proves (W1). Width enlargement therefore cannot improve the true variational bottom of this full class. It could change the quality of a particular sufficient estimate; that is a different issue. [ABSTRACT / PAPER, derivation here]

For an exact admissible finite trial space F, the variational direction is

\[
 \lambda(P,\delta)\le
 \min_{0\ne f\in F}\frac{\mathcal Q(f)}{\|f\|^2}.          \tag{W2}
\]

Use the form-domain extension when the trial generators are not smooth; its source/core identification is an additional prerequisite. Floating-point error comes after this variational distinction. Thus `0.0008` is not a proved lower margin, even if its finite assembly is accurate. Different rescaled degree-three trial spaces need not themselves be nested as width changes. [ABSTRACT / PAPER]

The table does not establish a limit of zero, eventual positivity, a decay rate, or the absence of a uniform positive floor. Those assertions need additional estimates. Once lobes overlap, the norm must remain the physical Gram norm or a quotient by the synthesis kernel. The parent already refutes a positive product-profile-norm floor after fixed-width overlap; [W]'s inclusion of cross-Gram terms is the correct convention, not a substitute for controlling its small directions. [C, Section 5.1; ABSTRACT / PAPER; numerical stability unverified]

## 3. Which loss is actually forbidden?

The warning in [W, line 15] is useful as a **method-selection warning**: a fixed absolute error can consume a shrinking margin. Its statement that only exact representations or direction-wise domination have room is not an exhaustive mathematical theorem.

A simple algebraic control separates these claims. For every integer n >= 1, let

\[
 A_n=(1+n^{-1})I,\qquad B_n=I,\qquad A_n-B_n=n^{-1}I.
\]

The deliberately lossy, separately proved estimates

\[
 A_n\succeq(1+3/(4n))I,\qquad B_n\preceq(1+1/(4n))I
\]

still certify

\[
 A_n-B_n\succeq(2n)^{-1}I>0.                             \tag{W3}
\]

This is a symbolic proof for all n, with nonzero losses and a margin tending to zero. It is **not** a model of the Weil source. It disproves only the general inference that shrinking margins eliminate every lossy method. For the actual source, the parent’s two-witness obstruction to its particular full-space scalar split remains intact. The algebraic control does not repair that split or transfer its witnesses into the harmonic-lift range. [ABSTRACT / PAPER; C, Section 6.3]

The admissible principle is therefore: **prove that the loss fits the available source budget, uniformly under the required quantifiers**. A bound losing a factor on the final positive margin is not the same as a bound losing that factor on one large summand before cancellation.

Likewise, independently proving `Q(f) >= -epsilon_n ||f||^2` for every f on each full exhausting support, with `epsilon_n -> 0`, is enough for the terminal fixed-test limit. It need not be an exact square identity. This is an alternative consumer interface, not a claim that the original exact head target has been closed. [C, consumer contract; COFINAL_FAMILY / PAPER, conditional implication]

## 4. The unchanged source-defined target

Keep the parent’s exact harmonic lift, not a raw coefficient vector or the WIDTH packet:

\[
 f=\mathcal L_nz=v_z-(B_n+n^{-1}I)^{-1}E_nz.
\]

Here B_n is the already coercive tail operator, E_n the full head-to-tail cross map, and G_n the physical head Gram. Define exactly as in [C, (38)–(39)]

\[
 \mathcal P_n[z]=\mathcal D(f)+2|M_c(f)|^2+n^{-1}\|f\|^2,
\]
\[
 \mathcal N_n[z]=c_A\|f\|^2+
 2\sum_{m\le e^{2n}}\frac{\Lambda(m)}{\sqrt m}C_f(\log m)
 +2|M_s(f)|^2.                                          \tag{W4}
\]

Here `D(f)=int_0^infty A(t)||U_t f-f||^2 dt`, `A(t)=e^(-t/2)/(1-e^(-2t))`, `c_A=gamma_E+log(8pi)+pi/2`, `C_f(t)=Re <f,U_t f>`, and `M_c,M_s` integrate f against `cosh(x/2),sinh(x/2)`. Lambda is the von Mangoldt weight. N is signed; its name does not assert positivity.

The unpaid inequality remains

\[
 \boxed{\forall n\ge1\ \forall z\in V_n:\quad
                      \mathcal N_n[z]\le\mathcal P_n[z].} \tag{W5}
\]

The positive energy P is source-defined. On a nonzero head vector it satisfies `P_n[z] >= n^(-1) z*G_n z > 0`. Consequently an equivalent directional diagnostic is

\[
 \rho_n=\sup_{z\ne0}\frac{\mathcal N_n[z]}{\mathcal P_n[z]},
 \qquad \rho_n\le1.                                    \tag{W6}
\]

This retains the same direction on both sides instead of comparing unrelated extremizers. **Neither (W5) nor its all-n bound (W6) is proved here.** A new notation or a list of computed ratios is not the universal mechanism. [C, (38)–(42); ABSTRACT / PAPER for equivalence; COFINAL_FAMILY / CONDITIONAL for target]

An exact series `B_(0,n) + sum_k C_(n,k)` with positive C terms also remains admissible. But its signed base, source identity, common coordinate transport, and uniform stopping argument must be supplied. The parent’s exact control `B_0=-1`, `C_k=2^(-k)` has sum zero while every finite lower sum is negative. Exact positive summands alone do not finish a finite proof. [C, Section 6.1; ABSTRACT / PAPER]

The approximate `n=3.9` comparison in [W] is not a canonical-head certificate. Canonical n is an integer with a specified support embedding. After centering these lobes the outer radius is `(log P+2delta(P))/2`. A finite packet above `-1/n` says nothing about omitted functions on that full interval. If actual nonnegativity is proved on every full support, no positive-floor decay rate is needed. [ABSTRACT / PAPER]

## 5. Next action, alternatives, and prediction closeout

**The next task does not change:** the parent’s paper audit of its endpoint payment and ordinary-mean-zero tail comes before any enlargement. The fixed-width full six-profile head remains the missing local comparison. WIDTH does not transfer the `47/6000` tail constant or `6000/41` residual coefficient to its wider supports. [C, Sections 4 and 8; ABSTRACT / PAPER as inherited, independent review pending]

| Representation | Decisive object | Decision value / cost, ordinal |
|---|---|---|
| Directional energy compensation | Same-vector comparison (W5), including all mixed terms and the harmonic lift | 10/10 / unknown for an all-n proof |
| Source positive-series or innovation identity | Explicit base payment and symbolic all-n transport; positive increments alone are insufficient | 9/10 / unknown for an all-n proof |

These are candidate representations, not authorizations for larger runs.

**Cheapest decisive check and sole retained CODEX directive:** independently audit [C, Theorems 3–4 and (29)] at the frozen original width, including every endpoint and the six-dimensional head. Preserve its existing success and failure gates. Do not rerun WIDTH, change a profile, edit Lean, or restart a packet sweep under this supplement.

**DISCRIMINATOR:** on the original six-profile geometry use the full-residual lower and upper head envelopes [C, (30)–(31)]. A lower envelope >= 0 certifies the declared target. A strict negative upper envelope at c=0 supplies a source counterexample. A zero-straddling enclosure remains inconclusive. Finite packet positivity and the WIDTH table supply neither envelope.

All frozen COMPENSATE prediction scores remain unchanged. In particular, WIDTH is not an independent review of the endpoint theorem, the `47/6000` tail, or the two-witness obstruction. The prospective registrations `P_COMP_ENDPOINT_PROOF_SURVIVES_REVIEW` (0.90), `P_COMP_MEAN_ZERO_TAIL_SURVIVES_REVIEW` (0.86), and `P_COMP_TWO_WITNESS_SCALAR_OBSTRUCTION_SURVIVES` (0.95) remain pending on this evidence.

New prospective, post-data registration: `P_WIDTH_VARIATIONAL_SCOPE_REVIEW`, probability 0.98. Exact event: an independent paper review accepts (W1)–(W3) with the stated physical-norm and trial-space boundaries. Not scored in this supplement. No numerical experiment or blind forecast is claimed.

## 6. Dependency record and publication handoff

**DOWNSTREAM_CONSUMER:** full compact-smooth Weil nonnegativity. **ACTUAL_CONSUMER_REQUIREMENT:** that sign on every required test, or the proved full-space vanishing-negative-error interface. **ORIGINAL_REQUESTED_OBJECT:** WIDTH’s implications for the existing compensation mechanism. **ORIGINAL_OBJECT_IS:** growing-width repair and a universal exact-square representation are NOT_NECESSARY interfaces.

**KNOWN_WEAKER_INTERFACES:** (W5); complete residual head bounds with their proved tails; an independently derived all-n innovation rule; full-support lower errors tending to zero. **FAILURE_TYPE:** NO_DERIVATION for universal source compensation. **EPISTEMIC_STATUS:** RESEARCH_DEBT, not route death. **REOPEN_TRIGGER:** a source-derived all-n comparison or a certified strict negative source witness. **NOVELTY_AXIS:** evidence and quantifier discipline, not a new global sign theorem.

**Closeout:** the data strengthen the case against using wider lobes as a floor-improvement tactic. No analytic supplier closes, and no new claim of mathematical impossibility follows from the table. The missing object is still the full directional comparison. Do not replace a finite Rayleigh upper approximation by a class lower certificate or impose a fixed loss budget without proving its adequacy.

Only this new supplement is written. The parent verdict, source addenda, code, queue, and shared state remain unchanged. Branch: `rh_clean`. Commit SHA and readback blob are supplied in the delivery receipt. Lean files written: none. Lean gate commands and axiom profile: not applicable to this document-only intake. Publication verifies bytes, not mathematics.
