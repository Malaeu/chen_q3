# STATUS: OPEN — ONE-INPUT RECIPROCAL-MODE SHELL FOUND; NO ZERO-OPEN SHELL
```yaml
PRIMARY: TRY_P59_RECIPROCAL_MODE_XI_LATTICE_ERROR_ENERGY_BOUND
PRIMARY_COUNT: 1
STATUS: OPEN
OPERATIVE_CLASS: TRY_RECIPROCAL_MODE_WEIGHTED_L2_SOURCE_BOUND

REQUEST_LOCK:
  REQUEST_ID: REQ-2026-09-03-SHELLSEARCH
  BOUNDARY_ID: GOAL058_SHELL_SEARCH_SOURCE_TO_LATTICE_ATOM
  REQUEST_COMMIT: c1bb9cdea0de351c3b67d185b0b645960f15eb6f
  REQUEST_PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_SHELL_SEARCH_SOURCE_TO_LATTICE_ATOM_2026-09-03.txt
  REQUEST_GIT_BLOB: 71e2223631e2059457d07edcdf7c50d87aa5b598
  REQUEST_SHA256: 47080558c7b75f922966c68b8ba50c7001e996fccf8ac6b7bad1dd45845e73c4
  REQUEST_BYTES: 6855
  REQUEST_LINES: 95
  FINAL_LF: true
  ATTACHMENT_MATCHES_COMMITTED_BYTES: true

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  SOURCE_BASE_COMMIT_SHORT: 0673693e
  SOURCE_BASE_COMMIT: 0673693e0e3ff6451d88b2975a8ff0d15392d206
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SHELL_SEARCH_SOURCE_TO_LATTICE_ATOM_2026-09-03.md
  REVIEW_BOUNDARY: PAPER_SHELL_SEARCH_ONLY
  WRITE_SCOPE: VERDICT_DOC_ONLY

PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_G1_G3_COFINAL_GROUND_TRACKING
  SOURCE_OBJECT_FAMILY_ID: PROPOSITION59_CCM_FINITE_BOTTOM_GROUND_FAMILY
  TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false

TOP_SHELL:
  CODE: P59_RECIPROCAL_MODE_WEIGHTED_L2_SHELL
  OUTPUT: [COMPONENT_N, COMPONENT_I]
  OPEN_INPUT_COUNT: 1
  NEW_ATOM: P59_RECIPROCAL_MODE_XI_LATTICE_ERROR_ENERGY_BOUND
  NEW_ATOM_FORMULA: "sum_{n=1}^{N_k} |Delta_{k,n}|^2 / n^2 <= C / L_k^4"
  SOURCE_COORDINATE: "R_k = diag(1/n), so the left side is norm(R_k Delta_k)^2"
  LOGICALLY_WEAKER_THAN_OLD_TWO_COMPONENT_ATOM: false
  STRUCTURALLY_SMALLER_THAN_P59_XI_LATTICE_LOW_MODE_STABILITY_IDENTITY: true
  RH_CIRCULAR: false

TOP_SHELL_CONSEQUENCES:
  NORMALITY_WEIGHT:
    formula: "W_k <= (pi/sqrt(6))*sqrt(C)/L_k^2"
  IDENTIFICATION:
    formula: "sup_{1<=n<=X L_k/(2 pi)} |Delta_{k,n}| <= X*sqrt(C)/(2 pi L_k)"
  COVERAGE_GUARD: "N_k/L_k -> infinity"

SHELL_RANKING:
  - rank: 1
    code: P59_RECIPROCAL_MODE_WEIGHTED_L2_SHELL
    open_inputs: 1
    first_open_cost: 2/10
    kill_power: 10/10
  - rank: 2
    code: P59_DISCRETE_HARDY_GRADIENT_SHELL
    open_inputs: 1
    first_open_cost: 3/10
    kill_power: 9/10
  - rank: 3
    code: P59_FULL_LATTICE_SUP_SHELL
    open_inputs: 1
    first_open_cost: 5/10
    kill_power: 8/10
  - rank: 4
    code: P59_NORMALIZED_XI_LATTICE_EIGEN_EQUATION_SHELL
    open_inputs: 2
    first_open_cost: 2/10
    kill_power: 10/10
  - rank: 5
    code: P59_SOURCE_PICK_RECIPROCAL_COERCIVITY_SHELL
    open_inputs: 2
    first_open_cost: 2/10
    kill_power: 9/10
  - rank: 6
    code: CCM_PROJECTIVE_PROLATE_ONE_RATE_SHELL
    open_inputs: 2
    first_open_cost: 5/10
    kill_power: 9/10
  - rank: 7
    code: WEIL_FORM_MOSCO_MINIMIZER_SHELL
    open_inputs: 3
    first_open_cost: 3/10
    kill_power: 8/10

ZERO_OPEN_SHELL:
  FOUND: false
  STATUS: NO_RECOGNIZED_SOURCE
  MATHEMATICALLY_IMPOSSIBLE_CLAIMED: false
  REASON: "S1-S9 contain no proved comparison between the finite ground row and Xi samples; S7 concerns a different trial family and S8 still needs a rate."

CCM_IMPLIED_SHELL:
  CODE: CCM_PROJECTIVE_PROLATE_ONE_RATE_SHELL
  OPEN_INPUTS:
    - FINITE_TRIAL_TO_CCM_CONTINUUM_TRIAL_CROSSWALK
    - P59_COMMON_ANCHOR_PROJECTIVE_ONE_RATE
  ONE_RATE: "|A_k| * L_k^(5/2) * sqrt(p_k) = O(1)"
  RELATION_TO_TOP_SHELL: STRICTLY_STRONGER_AS_SOURCE_COMMITMENT
  REASON: "It controls a full ground-to-trial projective distance and commits to the CCM trial intermediary; the top shell controls only the reciprocal-mode Xi-sample observable."

FULL_CHAIN_COUNTS:
  NEW_ANALYTIC_OPEN_INPUTS: 2
  LEAN_BOOKKEEPING_OPEN_TRANSACTIONS: 2
  TOTAL_OPEN_REPOSITORY_OBLIGATIONS: 4
  ANALYTIC:
    - COFINAL_SIMPLE_EVEN_FINITE_GROUND
    - P59_RECIPROCAL_MODE_XI_LATTICE_ERROR_ENERGY_BOUND
  LEAN:
    - P59_RECIPROCAL_MODE_WEIGHTED_L2_AND_ALTERNATING_CURVATURE_SHELL
    - P59_MOVING_LATTICE_MONTEL_VITALI_COMPOSITION

PREDICTION_FATES:
  P_A_SHELL_WITH_ZERO_OPEN_INPUTS_EXISTS:
    probability: 0.10
    fate: REFUTED_BY_AUDITED_SOURCE_SEARCH
    scope: COFINAL_FAMILY
    verifier: PAPER
  P_BEST_SHELL_HAS_ONE_OPEN_INPUT:
    probability: 0.55
    fate: CONFIRMED
    scope: ABSTRACT
    verifier: PAPER
  P_JUDGE_TOP_SHELL_MATCHES_OBSERVER_SEALED:
    probability: 0.35
    fate: REFUTED
    scope: ABSTRACT
    verifier: PAPER
    note: "The sealed candidate is a Weil-energy pinning mechanism for I only; it is circular without an on-line positive zero sum. The selected shell is an unconditional norm embedding for N and I."

SEALED_COMPARISON:
  READ_AFTER_Q1_Q4_FIXED: true
  SEALED_PATH: docs/routeB_bus/sealed/OBSERVER_SEALED_SHELL_CANDIDATE_2026-09-03.md
  SEALED_GIT_BLOB: 4ac581703b945c9e64f495e1869e5fc7db3630de
  RELATION: DISJOINT_AND_DOMINATED_AT_INTERFACE
  SEALED_SURVIVES: false

SCOPED_KILLS:
  WEIL_ENERGY_PINNING_WITHOUT_RH_SIGN:
    CODE: KILL_SMALL_WEIL_ENERGY_TO_POINTWISE_ZERO_PINNING
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: INDEFINITE_HERMITIAN_ZERO_SUM
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
  KREIN_WEYL_TITCHMARSH_GLOBAL_POSITIVE_SHELL:
    CODE: KILL_GLOBAL_HERBLOTZ_SHELL_AS_RH_CIRCULAR
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: SOURCE_ASSUMPTION_A_INFINITY_POSITIVE_IMPLIES_RH
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_AS_UNCONDITIONAL_SHELL
  SUZUKI_STRONG_RESOLVENT_AS_AVAILABLE_THEOREM:
    CODE: KILL_STRONG_RESOLVENT_IMPORT_AS_UNPROVED
    KILL_SCOPE: ATTEMPT
    KILL_EVIDENCE_KIND: PRIMARY_SOURCE_LABELS_IT_EXPECTED
    EPISTEMIC_STATUS: RESEARCH_DEBT
  GENERIC_LOEWNER_TO_LATTICE_RATE:
    CODE: DO_NOT_REOPEN_GENERIC_LOEWNER_RATE
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: PRIOR_TWO_BY_TWO_PLANT
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD

DEPENDENCY_EPISTEMICS:
  DOWNSTREAM_CONSUMER: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  ACTUAL_CONSUMER_REQUIREMENT: "The same normalized entire real-zero ground family converges locally uniformly to centeredXi."
  ORIGINAL_REQUESTED_OBJECT: "Two-component lattice atom N plus I"
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACES:
    - "direct bounded curvature plus moving-lattice identification"
    - "direct local boundedness plus moving-lattice identification"
    - "direct TendstoLocallyUniformlyOn"
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: "reciprocal-mode negative-Sobolev error as one scalar source-facing atom"

LEAN_READY:
  - P59_RECIPROCAL_MODE_WEIGHTED_L2_SHELL
  - P59_DISCRETE_HARDY_GRADIENT_SHELL
  - P59_FULL_LATTICE_SUP_SHELL
  - P59_WEIGHTED_ERROR_TO_CURVATURE_BOUND
  - P59_MOVING_LATTICE_UNIQUE_CLUSTER_COMPOSITION

NEW_ANALYTIC_WORK:
  - COFINAL_SIMPLE_EVEN_FINITE_GROUND
  - P59_RECIPROCAL_MODE_XI_LATTICE_ERROR_ENERGY_BOUND

CHEAPEST_NEXT_ACTION:
  TASK_ID: GOAL058_RECIPROCAL_MODE_XI_LATTICE_ENERGY_SOURCE_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  RELATION_TO_EXISTING_PREFLIGHT: "Refines, does not replace, GOAL058_NORMALIZED_XI_LATTICE_EIGEN_EQUATION_PREFLIGHT."
  REGISTERED_PREDICTION:
    name: P_LOW_MODE_RECURRENCE_CLOSES_BEFORE_GAP
    probability: 0.40
  SUCCESS: P59_RECIPROCAL_MODE_XI_LATTICE_ENERGY_IDENTITY
  FAILURE: P59_XI_LATTICE_EQUATION_REIMPORTS_DENSE_TAIL_OR_GAP
  FALSIFIER: "Reject any derivation whose first quantitative step is a full inverse, an absolute/odd floor, or the desired energy bound under another name."

LEAN_EDIT_PERFORMED: false
NUMERICAL_RUN_PERFORMED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
HONESTY_STATE: CHALLENGER_NOT_RH
BUS_010: VOID

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
CURRENT_SMALLEST_GAP: P59_RECIPROCAL_MODE_XI_LATTICE_ERROR_ENERGY_BOUND
```

## ROUTE MAP

| Rank | Shell | Conclusion | Open inputs | First decisive failure | Circularity | Tags |
|---:|---|---|---:|---|---|---|
| 1 | `P59_RECIPROCAL_MODE_WEIGHTED_L2_SHELL` | N + I | 1 | source cannot control `diag(1/n)·Delta` before a full inverse or dense tail | no | `[COFINAL_FAMILY][CONDITIONAL]` |
| 2 | `P59_DISCRETE_HARDY_GRADIENT_SHELL` | N + I through rank 1 | 1 | adjacent-mode difference estimate does not follow from the dense Loewner equation | no | `[COFINAL_FAMILY][CONDITIONAL]` |
| 3 | `P59_FULL_LATTICE_SUP_SHELL` | N + I | 1 | asks for the strongest uniform profile directly | no | `[COFINAL_FAMILY][CONDITIONAL]` |
| 4 | `P59_NORMALIZED_XI_LATTICE_EIGEN_EQUATION_SHELL` | rank-1 atom | 2 | source stability reimports the collapsed complement inverse | no if the inverse is avoided | `[COFINAL_FAMILY][CONDITIONAL]` |
| 5 | `P59_SOURCE_PICK_RECIPROCAL_COERCIVITY_SHELL` | rank-1 atom | 2 | no canonical source Pick/operator-monotone interpolant is proved | no if source-defined | `[COFINAL_FAMILY][CONDITIONAL]` |
| 6 | `CCM_PROJECTIVE_PROLATE_ONE_RATE_SHELL` | N + I | 2 | finite-trial crosswalk and projective rate are both open | no | `[COFINAL_FAMILY][CONDITIONAL]` |
| 7 | `WEIL_FORM_MOSCO_MINIMIZER_SHELL` | N + I | 3 | no common-space large-window Mosco limit or unconditional Xi minimizer | circular if global Weil positivity is imported | `[COFINAL_FAMILY][CONDITIONAL]` |

No shell with zero open inputs was found. This is a `NO_SOURCE` result, not a proof that no undiscovered theorem can exist.

## SOURCE LOCATOR LEDGER

| Source | Exact locator | What it supplies | Status |
|---|---|---|---|
| P59 sampling | `Q3/Proofs/RouteB/Proposition59EntireTransform.lean`: `proposition59RawTransform_at_lattice`, `proposition59RawTransform_at_zero_eq_sqrt` | S3, exact node and anchor values | `PROVEN_IN_PROJECT` `[FINITE_CELL][LEAN]` |
| Source displacement | `Q3/Proofs/RouteB/CCMFiniteWeilSourceCommutator.lean`: `ccmWeilMatFinite_structured_offdiag`, `ccmWeilMatFinite_commutator` | S4, divided differences and rank-two displacement | `PROVEN_IN_PROJECT` `[FINITE_CELL][LEAN]` |
| P59 curvature/product | `Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean`: `proposition59Curvature_eq_root_sum_add_tail`, `proposition59_compact_envelope`, `proposition59_normalized_bound_on_ball` | S5, real curvature and local envelope | `PROVEN_IN_PROJECT` `[FINITE_CELL][LEAN]` |
| Alternating lattice form | `PROSHKA_VERDICT_GOAL058_ALTERNATING_LATTICE_FORM_OF_THE_CURVATURE_WALL_2026-09-03.md`, commit `f788d2fa` | S6 and the current N/I split | `PROVEN_ON_PAPER` `[FINITE_CELL][PAPER]` |
| Same-family composer | `Q3/Proofs/RouteB/SameFamilyGroundTrialCompositionCore.lean`: `sameFamilyGroundTrialCompositionCore` | exact additive ground/trial error composition | `PROVEN_IN_PROJECT` `[ABSTRACT][LEAN]` |
| Projective transfer | `Q3/Proofs/RouteB/WeightedProjectiveEvaluationTransfer.lean`: `tendstoUniformlyOn_zero_of_weighted_projective_defect` | abstract phase-aligned projective transfer | `PROVEN_IN_PROJECT` `[ABSTRACT][LEAN]` |
| Terminal consumer | `Q3/Proofs/RouteB/Goal058DirectGroundZeroEscape.lean`: `rh_of_real_zero_family_tendsto_centeredXi` | real-zero local-uniform limit implies `Q3.RH` | `PROVEN_IN_PROJECT` `[ABSTRACT][LEAN]` |
| CCM finite real-zero theorem | Connes–Consani–Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1, Theorem 1.1 / Theorem 5.10 | S2 under simple-even normalization | `PROVEN_IN_LITERATURE` `[FINITE_CELL][PAPER]` |
| CCM trial limit | same paper, Lemma 7.3 and §8 | continuum trial transform tends to Xi; names ground/trial approximation as missing | `PROVEN_IN_LITERATURE` / crosswalk `OPEN` `[COFINAL_FAMILY][PAPER]` |
| Continuous real-zero engine | Connes–van Suijlekom, *Quadratic Forms, Real Zeros and Echoes of the Spectral Action*, arXiv:2511.23257 | simple isolated even lowest eigenfunction has real-zero Fourier transform | `PROVEN_IN_LITERATURE` `[ABSTRACT][PAPER]` |
| Localized Weil operator | Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096v2, Theorems 1.1, 1.3, 1.4 | operator realization, continuity, small-window simple-even | `PROVEN_IN_LITERATURE` `[ABSTRACT][PAPER]` |
| Large-window operator limit | Suzuki, §7.5 | strong-resolvent limit is stated as expected | `CONJECTURAL` `[COFINAL_FAMILY][CONDITIONAL]` |
| Finite explicit-formula dictionary | Groskin, *A finite Guinand–Weil dictionary...*, arXiv:2607.02828, Theorem 2.5 and Corollary 3.3 | exact finite coefficient-to-zero-sum transport and tail certification | `PROVEN_IN_LITERATURE` `[FINITE_CELL][PAPER]` |
| Discrete Hardy shell | classical discrete Hardy inequality | H2: discrete gradient controls reciprocal weighted norm | `RECOGNIZED_THEOREM`; exact Mathlib API not pinned `[ABSTRACT][PAPER]` |

## Q1 — SHELL LIST

### H1 — `P59_RECIPROCAL_MODE_WEIGHTED_L2_SHELL`

Put

\[
f(z)=\frac{\operatorname{centeredXi}(z)}
          {\operatorname{centeredXi}(0)},\qquad
\Delta_{k,n}=f_k(x_{k,n})-f(x_{k,n}),
\]

and

\[
\mathcal E_k^2
=\sum_{n=1}^{N_k}\frac{|\Delta_{k,n}|^2}{n^2}.
\]

The exact shell is:

\[
\boxed{
\mathcal E_k^2\le \frac{C}{L_k^4}
\Longrightarrow
\begin{cases}
W_k\le\dfrac{\pi\sqrt C}{\sqrt6\,L_k^2},\\[2mm]
\displaystyle
\sup_{1\le n\le X L_k/(2\pi)}
|\Delta_{k,n}|
\le\dfrac{X\sqrt C}{2\pi L_k}
\to0
\quad(\forall X>0).
\end{cases}}
\]

The second line is read after the production coverage guard
\(N_k/L_k\to\infty\).

**Inputs.** Exact normalized samples and the production schedule are source-locked in S3. Finite Cauchy–Schwarz and \(\sum_{n\ge1}n^{-2}=\pi^2/6\) are classical; the project already imports the Basel sum as `hasSum_zeta_two`. The only open input is

\[
\boxed{
\sum_{n=1}^{N_k}\frac{|\Delta_{k,n}|^2}{n^2}
=O(L_k^{-4}).
}
\]

**Mechanism.** Cauchy–Schwarz gives
\(W_k\le\mathcal E_k(\sum n^{-2})^{1/2}\).
Each coordinate satisfies \(|\Delta_{k,n}|\le n\mathcal E_k\).
At physical radius \(X\), the relevant indices satisfy \(n=O_X(L_k)\).

**First failure.** The exact source equation has not yet produced this weighted energy without a full inverse or an uncontrolled dense tail.

**Circularity.** None. The target uses the independently defined classical `centeredXi`; no RH property of its zeros is assumed.

A family of similar shells exists with weight \(n^{-2a}\), \(1\le a<3/2\). The choice \(a=1\) is canonical here because S4 already exposes the reciprocal-mode diagonal \(R=\operatorname{diag}(1/n)\).

### H2 — `P59_DISCRETE_HARDY_GRADIENT_SHELL`

Let \(\Delta_{k,0}=0\), which follows from the common normalization at the central node. If

\[
\sum_{n=1}^{N_k}
|\Delta_{k,n}-\Delta_{k,n-1}|^2
\le \frac{C}{L_k^4},
\]

the finite discrete Hardy inequality gives

\[
\sum_{n=1}^{N_k}\frac{|\Delta_{k,n}|^2}{n^2}
\le
4\sum_{n=1}^{N_k}
|\Delta_{k,n}-\Delta_{k,n-1}|^2.
\]

H1 then supplies N and I.

**Inputs.** The central normalization is S3. The finite discrete Hardy inequality is classical. One source estimate, the displayed discrete-gradient rate, is open.

**First failure.** The CCM matrix is dense. Its divided-difference law controls matrix entries, but no proved adjacent-mode recurrence controls this gradient.

**Circularity.** None.

### H3 — `P59_FULL_LATTICE_SUP_SHELL`

If

\[
\sup_{1\le n\le N_k}|\Delta_{k,n}|
\le \frac{C}{L_k^2},
\]

then

\[
W_k\le \frac{\pi^2C}{6L_k^2},
\]

and I holds immediately on every growing compact index range.

**Inputs.** Only the displayed sup-rate is open; S3 supplies the exact samples.

**First failure.** This is stronger than H1 and does not expose a quadratic source object. Probe 9 supports it only on finitely many cells.

**Circularity.** None.

### H4 — `P59_NORMALIZED_XI_LATTICE_EIGEN_EQUATION_SHELL`

Let

\[
x_{k,n}=\frac{\xi_{k,n}}{\xi_{k,0}},\qquad
y_{k,n}=(-1)^n f(x_{k,n}^{\rm pole}),
\]

so that \(|x_{k,n}-y_{k,n}|=|\Delta_{k,n}|\). For \(u_0=1\), define the center-normalized residual

\[
\mathcal R_k(u)_n
=(\widetilde K_ku)_n-u_n(\widetilde K_ku)_0.
\]

The ground row satisfies \(\mathcal R_k(x_k)=0\). A typed shell is:

\[
\boxed{
\|R_k(x_k-y_k)\|_2
\le C_k\|\mathcal R_k(y_k)\|_{\mathcal Y_k},
\quad
C_k\|\mathcal R_k(y_k)\|_{\mathcal Y_k}=O(L_k^{-2})
\Longrightarrow \text{H1},
}
\]

where \(R_k=\operatorname{diag}(1/n)\) and \(\mathcal Y_k\) must be source-defined.

**Inputs.** The eigen-equation and displacement structure are S1 and S4. The target residual estimate and reciprocal stability inequality are open.

**First failure.** Any proof beginning with
\(\|(\widetilde K_k-\lambda_{1,k})^{-1}\|\)
reopens a dead shape. The existing normalized-eigen-equation preflight is exactly the cheap discriminator.

**Circularity.** None if the stability estimate is proved from the finite source matrix without a global Weil-positivity or RH input.

### H5 — `P59_SOURCE_PICK_RECIPROCAL_COERCIVITY_SHELL`

Classical Loewner theory gives positivity of divided-difference matrices when the generating function is operator monotone. A source-specific shell would prove a canonical extension of the exact CCM beta-row to a Pick/complete-Bernstein function and derive

\[
\langle d,\mathcal L_k d\rangle
\ge c_k\|R_kd\|_2^2
\]

on the center-normalized tangent space. Combined with a dual estimate for
\(\mathcal R_k(y_k)\), this supplies H4 and hence H1.

**Inputs.** S4 is Lean-proved. A canonical source Pick function and the Xi-row residual rate are open.

**First failure.** A finite odd Hermite interpolant always exists but is noncanonical and does not establish operator monotonicity. Generic Loewner structure alone was already killed by the two-by-two plant.

**Circularity.** None if the source function is obtained from the explicit prime/archimedean formula; circular if positivity is imported from RH.

### H6 — `CCM_PROJECTIVE_PROLATE_ONE_RATE_SHELL`

Let \(q_k\) be the finite project trial row and let \(p_k\) be its phase-invariant projective defect from the normalized ground row. Assume:

1. the normalized finite-trial transforms converge locally uniformly to `centeredXi`;
2. on the same cofinal cells,
   \[
   |A_k|L_k^{5/2}\sqrt{p_k}=O(1).
   \]

Exact P59 node sampling and phase alignment then give a uniform ground-to-trial node error \(O(L_k^{-2})\). The trial limit gives the remaining trial-to-\(\Xi\) error on every fixed real compact. Hence H3, and therefore N and I.

**Inputs.** CCM Lemma 7.3 proves the continuum trial transform limit. The project proves the abstract projective transfer and the same-family additive composer. The finite-trial/continuum-trial normalization and projection crosswalk is open. The one-rate projective estimate is open.

**First failure.** Existing residual suppliers pay the collapsed absolute gap, and the current finite trial is not yet identified with the paper trial on one source-locked cofinal family.

**Circularity.** None.

### H7 — `WEIL_FORM_MOSCO_MINIMIZER_SHELL`

Suppose the normalized finite Weil forms are embedded into one Hilbert space, Mosco-converge to a limiting form, are equicoercive in a topology controlling reciprocal lattice samples, and the limit has a unique normalized minimizer whose transform is `centeredXi`. Standard convergence of minimizers then gives H1, and with stronger compact control gives H3.

**Inputs.** Lower-semicontinuity, finite form cores and existence of ground states are in CCM/Suzuki. Common-space large-window Mosco convergence, reciprocal equicoercivity and identification of the limiting minimizer are open.

**First failure.** Suzuki describes the large-window strong-resolvent limit as expected, not proved. A proof identifying the global minimizer through global Weil positivity is RH-circular.

**Circularity.** Conditional: noncircular only if all three open inputs are proved independently of global Weil positivity.

## Classical mechanisms audited but not promoted to shells

- **Laguerre–Pólya / Hadamard.** This is already consumed in source-specific form by S5: bounded curvature gives local boundedness. It supplies no source estimate of \(\Delta_{k,n}\).
- **Euler–Boole alternating quadrature.** It controls the signed Xi head and the explicit tail in S6. A signed alternating scalar cannot control the absolute \(W_k\) or growing-range sup without a new sign/variation theorem.
- **Yoshida–Bombieri–Suzuki localization.** These works give localized Weil forms, ground-state existence, continuity of the bottom eigenvalue, and small-window simple-even results. They do not provide the large-window Xi-sample profile. Suzuki proves simple-even only for sufficiently small windows, while the large-window operator limit is conjectural.
- **Krein strings / Weyl–Titchmarsh / global screw space.** The global positive/Herglotz object used to obtain the zeta spectrum assumes the global Weil positivity whose truth implies RH. It is circular as an unconditional shell.
- **Groskin’s finite Guinand–Weil dictionary.** It is an exact finite source-to-zero-sum transport and a valuable verifier. It gives no asymptotic pinning of the ground row to Xi samples.
- **Connes–van Suijlekom real-zero theorem.** It supplies S2; it does not control the lattice profile.
- **Small Weil energy \(\Rightarrow\) values small at zeta zeros.** This is false as an unconditional shell. The zero-side Hermitian sum is indefinite off the critical line; making it a sum of squares assumes the conclusion.

## Q2 — RANKING AND NEW ATOM

No zero-open shell exists in the audited project and primary-source corpus. This means `NO_RECOGNIZED_SOURCE`, not formal impossibility.

The best shell has exactly one open input:

\[
\boxed{
\texttt{P59\_RECIPROCAL\_MODE\_XI\_LATTICE\_ERROR\_ENERGY\_BOUND}
}
\]

with exact statement

\[
\boxed{
\exists C\ge0,\ \forall^\infty k,\qquad
\sum_{n=1}^{N_k}
\frac{
\left|
(-1)^n\frac{\xi_{k,n}}{\xi_{k,0}}
-
\frac{\operatorname{centeredXi}(x_{k,n})}
     {\operatorname{centeredXi}(0)}
\right|^2
}{n^2}
\le \frac{C}{L_k^4}.
}
\]

It is not a weaker assumption than N+I. It is stronger, because it controls both through one norm. It is nevertheless a smaller proof object than `P59_XI_LATTICE_LOW_MODE_STABILITY_IDENTITY`: one scalar quadratic envelope in the exact reciprocal-mode coordinates, with no committed inverse, recurrence, or intermediary trial family.

The existing normalized Xi lattice eigen-equation preflight remains the best candidate supplier search for this new atom. It is not replaced.

## Q3 — CCM’S IMPLIED SHELL

CCM Section 8 implicitly asks for the following project theorem:

```text
CCM_PROJECTIVE_PROLATE_ONE_RATE_SHELL

Given, on one source-locked cofinal family:
  ground rows xi_k and finite trial rows q_k;
  nonzero common anchors;
  exact P59 transforms F_ground,k and F_trial,k;
  a project crosswalk proving
    F_trial,k -> centeredXi locally uniformly;
  projective defects
    p_k = 1 - |<xi_k,q_k>|^2;
  the rate
    |A_k| L_k^(5/2) sqrt(p_k) = O(1);

then:
  W_k = O(L_k^-2);
  for every X>0,
    sup_{n <= X L_k/(2 pi)} |Delta_{k,n}| -> 0.
```

Status of its inputs:

| Input | Status |
|---|---|
| CCM continuum trial transform \(\to\Xi\) on closed substrips | `PROVEN_IN_LITERATURE`, Lemma 7.3 |
| Exact P59 node sampling | `PROVEN_IN_PROJECT` |
| Generic phase/projective transfer | `PROVEN_IN_PROJECT` |
| Same-family additive composition core | `PROVEN_IN_PROJECT` |
| Finite project trial \(\leftrightarrow\) CCM continuum trial crosswalk | `OPEN` |
| One-rate projective estimate | `OPEN` |

CCM explicitly names simple-even ground and sufficiently accurate trial-to-ground approximation as its two missing steps. Its qualitative shell is therefore H6. The typed project version above is stronger than CCM’s prose because it fixes one quantitative rate, one normalization and one cofinal family. It is stronger than H1 because it controls a full projective ground-to-trial error, while H1 asks only for one reciprocal-mode Xi-sample observable.

## Q4 — FULL TOP-SHELL COMPOSITION

| Step | Typed object / implication | Status | Open count |
|---:|---|---|---:|
| 1 | Production schedule \(m_k=N_k=k+2\), \(L_k=\log m_k\), \(N_k/L_k\to\infty\) | `PROVEN_IN_PROJECT/PAPER` | 0 |
| 2 | Exact entire P59 ground transform and node sampling | `PROVEN_IN_PROJECT` | 0 |
| 3 | Cofinal simple-even finite ground package | `OPEN_ANALYTIC` | 1 |
| 4 | Step 3 \(\Rightarrow\) `ZerosRealOn Set.univ F_k` | `PROVEN_CONDITIONAL` by CCM Thm. 5.10 and project bridge | 1 |
| 5 | `P59_RECIPROCAL_MODE_XI_LATTICE_ERROR_ENERGY_BOUND` | `OPEN_ANALYTIC` | 2 |
| 6 | Step 5 \(\Rightarrow\) components N and I | `PAPER_PROVED_HERE`, Lean-ready | 2 |
| 7 | N + S6 + bounded Xi alternating head + explicit tail \(\Rightarrow \sup_k\kappa_k<\infty\) | `PAPER_PROVED`, Lean-ready | 2 |
| 8 | Bounded \(\kappa_k\) \(\Rightarrow\) local boundedness of \(F_k/F_k(0)\) | `PROVEN_IN_PROJECT` | 2 |
| 9 | Local boundedness + I + entire-ness \(\Rightarrow\) local-uniform convergence to `centeredXi` | `PROVEN_CLASSICAL`, project composition OPEN | 2 |
| 10 | Real zeros + entire-ness + local-uniform convergence \(\Rightarrow Q3.RH\) | `PROVEN_IN_PROJECT`: `rh_of_real_zero_family_tendsto_centeredXi` | 2 |

The full route therefore has exactly:

```text
2 new analytic open suppliers:
  COFINAL_SIMPLE_EVEN_FINITE_GROUND
  P59_RECIPROCAL_MODE_XI_LATTICE_ERROR_ENERGY_BOUND

2 Lean bookkeeping transactions:
  reciprocal-mode/alternating-curvature shell
  moving-lattice Montel/Vitali composition

TOTAL unresolved repository obligations before the terminal consumer: 4.
```

## FINAL PROPOSAL

Select H1. The source-facing atom is now one negative-Sobolev energy:

\[
\|R_k\Delta_k\|_{\ell^2}^2=O(L_k^{-4}),
\qquad R_k=\operatorname{diag}(1/n).
\]

This is the only found shell with one open input that simultaneously supplies N and I while avoiding every dead representation.

Run one read-only source preflight. Substitute the exact Xi-sample row into the center-normalized eigen-equation and seek a source identity or one-sided estimate for \(\|R_k\Delta_k\|_2\). Preserve the previously registered probability `0.40`.

Success:

```text
P59_RECIPROCAL_MODE_XI_LATTICE_ENERGY_IDENTITY
```

Failure:

```text
P59_XI_LATTICE_EQUATION_REIMPORTS_DENSE_TAIL_OR_GAP
```

If it fails, use H2 as the first re-representation: control the discrete gradient and invoke Hardy. The second fallback is H6, the CCM projective-prolate shell.

## STRONGEST ATTACK

The new atom may be cleaner only because it hides the same difficulty inside a stronger norm. That objection is correct.

The repair is fail-closed:

- do not call H1 progress until a source expression for \(\|R_k\Delta_k\|_2^2\) is derived;
- reject any proof whose first estimate uses a full reduced resolvent, an absolute/odd floor, or the desired bound itself;
- if the source equation controls only a signed scalar, H1 has not been reached;
- if the weighted energy is not accessible, move to the discrete-Hardy shell rather than strengthening the norm again.

The sealed observer candidate does not repair this. Its small-Weil-energy step becomes pointwise pinning only after the zero-side form is made positive, which is RH-circular; it also supplies only I, not N.

## CODEX DIRECTIVE

No Lean execution is authorized by this paper-only request.

A later bounded transaction may be opened as:

```text
TASK_ID:
  GOAL058_RECIPROCAL_MODE_XI_LATTICE_ENERGY_SOURCE_PREFLIGHT

MODE:
  PAPER_AND_SOURCE_READ_ONLY

READ:
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceCommutator.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59EntireTransform.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean
  exact center-normalized ground equation used by the current lattice preflight

RETURN:
  1. exact target row y_k from centeredXi samples;
  2. exact residual R_k(y_k);
  3. an identity or inequality whose left side is
       sum |x_k-y_k|^2/n^2;
  4. the first uncontrolled source term;
  5. exactly one code:
       P59_RECIPROCAL_MODE_XI_LATTICE_ENERGY_IDENTITY
     or
       P59_XI_LATTICE_EQUATION_REIMPORTS_DENSE_TAIL_OR_GAP.

FORBIDDEN:
  Lean edits;
  numerical runs;
  full resolvent norms;
  absolute or odd-sector floors;
  pole/Arch-Prime splitting;
  post-hoc schedule changes.
```

## META CLOSEOUT

- **What became smaller?** Two lattice obligations became one scalar reciprocal-mode energy bound.
- **What was killed?** Unconditional pinning of pointwise zero values by small Weil energy; global Krein/Weyl–Titchmarsh positivity as a noncircular shell; strong-resolvent convergence as an available theorem.
- **What must not be tried again?** Generic Loewner-to-rate, full inverse estimates, or a zero-side sum of squares without RH.
- **Current smallest named gap:** `P59_RECIPROCAL_MODE_XI_LATTICE_ERROR_ENERGY_BOUND`.
- **Next cheapest decisive test:** source-only normalized Xi-row residual/energy preflight.
- **Prediction fates:** zero-open refuted by source audit; one-open confirmed; sealed-match refuted.
- **Memory entry:** use the reciprocal-mode negative-Sobolev error as the source-facing atom; current low-mode recurrence is a candidate supplier, not the atom itself.

No Lean source was edited. No numerical run was started. No route promotion or RH claim was made.
