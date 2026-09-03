# STATUS: OPEN — LINEAR EIGEN-EQUATION SHELLS EXHAUSTED; SOURCE-SPECIFIC REAL-ZERO QUASI-EIGENVECTOR SELECTION IS THE NEW ATOM
```yaml
PRIMARY: TRY_P59_SOURCE_SPECIFIC_REALZERO_QUASIEIGEN_SELECTOR
PRIMARY_COUNT: 1
STATUS: OPEN
OPERATIVE_CLASS: TRY_NONLINEAR_GROUND_ROW_IDENTIFICATION

REQUEST_LOCK:
  REQUEST_ID: REQ-2026-09-04-QUASIEIGEN
  BOUNDARY_ID: GOAL058_XI_ROW_QUASI_EIGENVECTOR_AND_COLLAPSE_THEOREM
  REQUEST_COMMIT: d0f217a7d2a5ba86bab57edc4f7a36d44faead94
  REQUEST_PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_XI_ROW_QUASI_EIGENVECTOR_AND_COLLAPSE_THEOREM_2026-09-04.txt
  REQUEST_GIT_BLOB: f5b26c7163f1e556f1e3881f8fdb7f331a3d55ae
  REQUEST_SHA256: fd98461bd5065dc76caf4e3d2cf21005dbfa6b94d1d1415c27cab1e102667722
  REQUEST_BYTES: 9249
  REQUEST_LINES: 104
  FINAL_LF: true
  ATTACHMENT_MATCHES_COMMITTED_BYTES: true

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  SOURCE_BASE_COMMIT_SHORT: c1a728ff
  SOURCE_BASE_COMMIT: c1a728ff24d96d1b923fa330729cff1251089372
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_XI_ROW_QUASI_EIGENVECTOR_AND_COLLAPSE_THEOREM_2026-09-04.md
  REVIEW_BOUNDARY: PAPER_ADJUDICATION_ONLY
  WRITE_SCOPE: VERDICT_DOC_ONLY

PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_G1_G3_COFINAL_GROUND_TRACKING
  SOURCE_OBJECT_FAMILY_ID: PROPOSITION59_CCM_FINITE_BOTTOM_GROUND_FAMILY
  TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false

Q1_QUASIEIGENVECTOR:
  REGISTERED_THEOREM_SHAPE:
    formula: "norm(R_m * residual_m(y_m)) <= C * 10^(-c*m)"
    status: NOT_DERIVED
  RATE_AUDIT:
    fixed_exponential_in_m_supported: false
    supplied_data_fit: "stretched exponential in m/log(m)"
    effective_base10_constants_for_m_over_log_m: [1.844, 2.064, 1.960, 2.014, 2.070]
    xi_gamma_factor_constant: "pi^2/(2*log(10)) = 2.143..."
    repaired_candidate: "norm(R_m * residual_m(y_m)) <= C*m^A*exp(-pi^2*m/(2*log(m)))"
  KNOWN_FROM_CCM_LEMMA_7_3: false
  KNOWN_FROM_GROSKIN_FINITE_DICTIONARY: false
  SOURCE_MECHANISM:
    status: OPEN_NEW_VECTOR_TRUNCATION_THEOREM
    required_identity: P59_XI_SAMPLE_ROW_AS_PERIODIZED_GLOBAL_NULL_ROW
    required_bound: P59_XI_ROW_WEIGHTED_VECTOR_TRUNCATION_RESIDUAL
  VERDICT: DEVELOP_WITH_RATE_REPAIR
  SCOPE: COFINAL_FAMILY
  VERIFIER: CONDITIONAL

Q2_GROUND_SELECTOR:
  REAL_ZEROS:
    generic_rigidity: MATHEMATICALLY_DEAD
    source_specific_selector: OPEN_BEST_CANDIDATE
    xi_row_transform_real_zero_status: UNKNOWN_NOT_IMPLIED_BY_RH
  EXACT_MINIMALITY:
    standalone_stability: MATHEMATICALLY_DEAD_WITHOUT_A_MODULUS
    joint_with_realzero_component: OPEN
  GLOBAL_ALTERNATING_SIGN_PATTERN:
    project_source: ABSENT
    status: LOW_VALUE_CHEAP_FALSIFIER
  BOUNDED_CURVATURE:
    supplies_normality: true
    supplies_vector_identification_alone: false
  STRONGER_SOURCE_PROVENANCE:
    candidate: "selfadjoint characteristic determinant component / strict interlacing / positive norming data"
    project_supplier: absent

NEW_ATOM:
  ID: P59_SOURCE_SPECIFIC_REALZERO_QUASIEIGEN_SELECTOR_MODULUS
  DEFINITION: >-
    omega_m(epsilon) is the supremum of norm(R_m*(v-y_m)) over center-normalized
    even source rows v whose P59 transform has the exact real-zero/characteristic
    property and whose weighted center-normalized residual is at most epsilon.
  TARGET: >-
    omega_m(C*m^A*exp(-pi^2*m/(2*log(m)))) = O((log m)^(-2)) on the production path.
  TARGET_MUST_NOT_ASSUME:
    - norm(R_m*(v-y_m)) is small
    - an absolute or relative complement floor
    - the desired locally uniform convergence
    - bounded curvature unless normality is being supplied separately

Q3_COLLAPSE:
  EXISTING_THEOREM_APPLIES_TO_FULL_CCM_BLOCK: false
  BECKERMANN_TOWNSEND_REASON: >-
    The Sylvester theorem requires separated spectral sets for the left and
    right displacement operators; the full CCM commutator has A=B=X and hence
    coincident spectral sets.
  SAME_SET_GENERIC_COLLAPSE: MATHEMATICALLY_DEAD
  EXACT_PLANT: >-
    Hermite interpolation realizes any positive diagonal matrix as a confluent
    same-node Loewner matrix, so same-node Loewner/displacement structure permits
    arbitrary singular-value profiles.
  ONE_SET_ANALOGUE:
    conclusion: "low rank of separated off-diagonal subblocks"
    does_not_imply: "decay of the full matrix spectrum or its smallest eigenvalue"
  PSD_HANKEL_THEOREM:
    applicable: false
    reason: "the CCM block is not supplied as a positive semidefinite Hankel matrix"
    rate_if_applicable: "rho^(-k/log(n)), not rho^(-k)"
  COLLAPSE_SOURCE_THEOREM: OPEN_NEW_ANALYTIC

Q4_SHELL_STATUS:
  H1_RECIPROCAL_ENERGY:
    exact_identity: true
    source_stability: false
    status: CLOSED_AS_NONDECISIVE_REPRESENTATION
  H2_DISCRETE_HARDY:
    inequality: classical
    source_gradient_supplier: absent
    status: CLOSED_AS_CURRENT_SOURCE_ATTEMPT
  H6_CCM_PROJECTIVE:
    abstract_transfer: valid
    current_supplier: pays_collapsed_gap
    status: OPEN_ONLY_AFTER_NEW_NON_GAP_SOURCE_THEOREM
  UNIVERSAL_NO_SOURCE_CLAIM: rejected_too_strong
  PRECISE_CLAIM: NO_LINEAR_SPECTRAL_STABILITY_SUPPLIER_FROM_CURRENT_EIGEN_EQUATION_REPRESENTATIONS
  ATOM_MOVES_TO_IDENTIFICATION: true
  CURRENT_SMALLEST_GAP: P59_SOURCE_SPECIFIC_REALZERO_QUASIEIGEN_SELECTOR_MODULUS

PREDICTION_FATES:
  P_ENERGY_IDENTITY_EXACT:
    probability: 0.90
    fate: CONFIRMED
    scope: FINITE_CELL
    verifier: PAPER
  P_S7_ODD_OFFDIAG_SMALL:
    probability: 0.55
    fate: REFUTED
    scope: FINITE_CELL
    verifier: ARB_INTERVAL
  P_ODD_FLOOR_FLAT:
    probability: 0.45
    fate: REFUTED
    scope: FINITE_CELL
    verifier: ARB_INTERVAL
  P_Q_AP_LT_1:
    probability: 0.35
    fate: REFUTED
    scope: FINITE_CELL
    verifier: ARB_INTERVAL
  P_RHO_STAB_FLAT:
    probability: 0.50
    fate: REFUTED
    scope: FINITE_CELL
    verifier: ARB_INTERVAL
  P_LOW_MODE_RECURRENCE_CLOSES_BEFORE_GAP:
    probability: 0.40
    fate: REFUTED_TWICE
    scope: COFINAL_FAMILY
    verifier: PAPER

  P_XI_ROW_QUASI_EIGEN_PROVABLE:
    probability: 0.65
    fate: UNRESOLVED_WITH_RATE_REPAIR
    scope: COFINAL_FAMILY
    verifier: CONDITIONAL
    note: >-
      A source mechanism is visible, but neither cited paper proves the
      source-locked vector residual, and the registered exp(-c*m) rate is not
      the natural rate indicated by the supplied data.
  P_REAL_ZEROS_RIGIDITY_IS_THE_SUPPLIER:
    probability: 0.35
    fate: REFUTED_AS_GENERIC_THEOREM_REPAIRED_SOURCE_SPECIFIC_SELECTOR_OPEN
    scope: ABSTRACT
    verifier: PAPER
  P_COLLAPSE_THEOREM_NOW:
    probability: 0.45
    fate: REFUTED
    scope: ABSTRACT
    verifier: PAPER
  P_ATOM_MOVES_TO_IDENTIFICATION:
    probability: 0.70
    fate: CONFIRMED_WITH_SCOPE_REPAIR
    scope: COFINAL_FAMILY
    verifier: PAPER

SCOPED_KILLS:
  GENERIC_REALZERO_NYQUIST_RIGIDITY:
    CODE: KILL_GENERIC_REALZERO_LATTICE_RIGIDITY
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXPLICIT_ROBIN_COSINE_PLANT
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
  MINIMALITY_TO_DISTANCE_WITHOUT_MODULUS:
    CODE: KILL_QUASIMINIMIZER_STABILITY_WITHOUT_GAP_OR_NONLINEAR_SELECTOR
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXACT_TWO_BY_TWO_COLLAPSED_OPERATOR_PLANT
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
  SAME_SET_DISPLACEMENT_TO_FULL_COLLAPSE:
    CODE: KILL_SAME_NODE_LOEWNER_STRUCTURE_TO_FULL_SPECTRAL_DECAY
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: CONFLUENT_HERMITE_DIAGONAL_PLANT
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
  BOUNDED_CURVATURE_AS_VECTOR_SELECTOR:
    CODE: KILL_ONE_SCALAR_CURVATURE_AS_GROUND_ROW_IDENTIFIER
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: AFFINE_LEVEL_SET_DIMENSION
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD

CANDIDATE_REPRESENTATIONS:
  R1_SOURCE_SPECIFIC_HYPERBOLICITY_SELECTOR:
    selected: true
    kill_power: 10/10
    preflight_cost: 2/10
    proof_cost_if_survives: 8/10
    discriminator: >-
      Determine whether the source-real-rooted admissible quasi-eigenvector set
      around the Xi row has R-weighted diameter tending to zero.
  R2_POLARIZED_ZERO_SIDE_VECTOR_RESIDUAL:
    selected: false
    kill_power: 9/10
    preflight_cost: 3/10
    proof_cost_if_survives: 7/10
    discriminator: >-
      Polarize the exact finite explicit-formula dictionary and prove that every
      component of R*residual(y) is an omitted-tail term with the repaired
      stretched-exponential envelope.
  R3_SOURCE_ANALYTIC_SYMBOL_COLLAPSE:
    selected: false
    kill_power: 8/10
    preflight_cost: 5/10
    proof_cost_if_survives: 9/10
    discriminator: >-
      Produce a source-defined analytic symbol or compact-kernel approximation
      for the entire CCM block; displacement rank alone is inadmissible.

CHEAPEST_NEXT_ACTION:
  TASK_ID: GOAL058_P59_REALZERO_QUASIEIGEN_SELECTOR_SOURCE_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  REGISTERED_PREDICTION:
    name: P_SOURCE_SPECIFIC_REALZERO_COMPONENT_IS_SELECTIVE
    probability: 0.30
  REQUIRED_OUTPUTS:
    - exact source predicate stronger than bare ZerosRealOn, if Theorem 5.10 supplies one
    - exact P59/Lagrange polynomial attached to the Xi-sample row
    - Robin-cosine Nyquist plant
    - a noncircular selector modulus omega_m
    - an interval-test design for the diameter of the admissible near-null set
  SUCCESS: P59_SOURCE_SPECIFIC_REALZERO_SELECTOR_SURVIVES_PLANTS
  FAILURE: P59_REALZERO_CONE_NOT_SELECTIVE
  FALSIFIER: >-
    A center-normalized even source row v at Xi-residual scale, with the same
    real-zero/characteristic property as the ground row, but with
    norm(R*(v-y_m)) bounded below independently of m.

DEPENDENCY_EPISTEMICS:
  DOWNSTREAM_CONSUMER: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  ACTUAL_CONSUMER_REQUIREMENT: >-
    The same normalized entire finite-ground family has only real zeros and
    converges locally uniformly to centeredXi on one cofinal path.
  ORIGINAL_REQUESTED_OBJECT: P59_RECIPROCAL_MODE_XI_LATTICE_ERROR_ENERGY_BOUND
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACES:
    - direct moving-lattice convergence plus bounded normalized curvature
    - direct local-uniform convergence
    - a source-specific selector modulus for real-rooted quasi-eigenvectors
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: nonlinear identification inside a collapsed quasi-eigenspace

LEAN_READY:
  - exact finite definition of the Xi-sample row and center-normalized residual
  - exact reciprocal coboundary and weighted energy identity
  - abstract selector-modulus implication to weighted lattice convergence
  - separated-subblock displacement identity
  - finite Robin-cosine anti-rigidity plant after its elementary root lemma is supplied

NEW_ANALYTIC_WORK:
  - P59_XI_SAMPLE_ROW_AS_PERIODIZED_GLOBAL_NULL_ROW
  - P59_XI_ROW_WEIGHTED_VECTOR_TRUNCATION_RESIDUAL
  - P59_SOURCE_SPECIFIC_REALZERO_QUASIEIGEN_SELECTOR_MODULUS
  - CCM_SOURCE_ANALYTIC_SYMBOL_SINGULAR_VALUE_DECAY

CODEX_DIRECTIVE:
  AUTHORIZED_NOW: false
  REASON: PAPER_ADJUDICATION_ONLY
  NEXT_TRANSACTION: GOAL058_P59_REALZERO_QUASIEIGEN_SELECTOR_SOURCE_PREFLIGHT
  FORBIDDEN:
    - Lean edits
    - numerical runs
    - full or reduced resolvent norms
    - absolute, relative, or odd-sector floors
    - assuming the selector conclusion in an admissibility predicate
    - applying Beckermann-Townsend with coincident spectral sets
    - post-hoc cofinal schedule changes

LEAN_EDIT_PERFORMED: false
NUMERICAL_RUN_PERFORMED: false
JUDGE_KERNEL_RERUN: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
HONESTY_STATE: CHALLENGER_NOT_RH
BUS_010: VOID

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
CURRENT_SMALLEST_GAP: P59_SOURCE_SPECIFIC_REALZERO_QUASIEIGEN_SELECTOR_MODULUS
```

## ROUTE MAP

| Route / object | Verdict | Decisive test | Main risk | Tags |
|---|---|---|---|---|
| Source-specific real-zero quasi-eigenvector selector | **PRIMARY, OPEN** | The admissible near-null set has \(R\)-diameter tending to zero | “Real zeros” may leave a large nonlinear family, just as the linear near-null space does | `[COFINAL_FAMILY][CONDITIONAL]` |
| Polarized explicit-formula residual | **OPEN SUPPORTING ROUTE** | Every component of \(R\mathcal R_m(y_m)\) becomes an omitted-tail functional | The scalar zero-sum dictionary may not polarize into the required vector identity with a useful rate | `[COFINAL_FAMILY][CONDITIONAL]` |
| Existing reciprocal energy / Hardy / projective shells | **EXHAUSTED IN THEIR CURRENT LINEAR FORMS** | A new supplier avoids every complement inverse | The same collapsing singular directions reappear under a renamed norm | `[COFINAL_FAMILY][PAPER]` |
| Displacement/Zolotarev collapse theorem | **NOT AVAILABLE FOR THE FULL BLOCK** | A source analytic-symbol theorem replaces coincident-set displacement | Off-diagonal compressibility is mistaken for full spectral collapse | `[COFINAL_FAMILY][CONDITIONAL]` |

## 1. Source lock and byte verification

The authoritative request was fetched at commit `d0f217a7d2a5ba86bab57edc4f7a36d44faead94`. Its Git blob is `f5b26c7163f1e556f1e3881f8fdb7f331a3d55ae`. Independent decoding of the blob gives exactly `9249` bytes, `104` newline-terminated lines, and SHA-256

```text
fd98461bd5065dc76caf4e3d2cf21005dbfa6b94d1d1415c27cab1e102667722
```

The six-field phase key is unchanged. `[COFINAL_FAMILY][PAPER]`

The convention card is binding: \(x_n=\xi_n/\xi_0\) and \(\Delta_n=x_n-y_n\) are full-mode ratios; \(R\) sends even rows to the odd sector; and the relevant energy is the odd-block form, not the noncentral even block. `[FINITE_CELL][PAPER]`

The supplied Probe-11 evidence verifies the finite identity to working precision while simultaneously showing why it cannot control \(\|R\Delta\|\): the quadratic value is as small as \(2.56\times10^{-134}\) although its expanded constituents remain near \(10^{-4}\)–\(10^{-6}\). This is finite diagnostic evidence, not a cofinal theorem. `[FINITE_CELL][ARB_INTERVAL]`

### 1.1 Source locator ledger

| Object | Exact locator | Status |
|---|---|---|
| Byte-exact request | `docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_XI_ROW_QUASI_EIGENVECTOR_AND_COLLAPSE_THEOREM_2026-09-04.txt` at `d0f217a7...` | `[COFINAL_FAMILY][PAPER]` |
| Basis and pairing convention | `docs/routeB_bus/CONVENTION_CARD_GOAL058.md` at `c1a728ff...` | `[FINITE_CELL][PAPER]` |
| Reciprocal energy derivation | `docs/routeB_bus/AGENT_REPORT_2026-09-04_GOAL058_RECIPROCAL_MODE_XI_LATTICE_ENERGY_SOURCE_PREFLIGHT.md`, especially §§1–3 and §12 | `[FINITE_CELL][PAPER]` |
| Independent finite diagnostic | `docs/routeB_bus/phase5_codex/out/odd_floor.md`, Probe 11 | `[FINITE_CELL][ARB_INTERVAL]` |
| Exact finite source displacement | `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceCommutator.lean`: `ccmWeilTau_structured_offdiag`, `ccmWeilMatFinite_commutator` | `[FINITE_CELL][LEAN]` |
| Conditional real-zero transfer | `q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59GroundLagrangeZeroSetBridge.lean`: `proposition59CCMTransform_zerosRealOn_of_lagrange` and its ground wrapper | `[FINITE_CELL][LEAN]` |
| Finite alternating curvature layer | `q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59AlternatingLatticeCurvature.lean` | `[FINITE_CELL][LEAN]` |
| CCM spectral programme | Connes–Consani–Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1, Lemma 7.3 and §8 | `[COFINAL_FAMILY][PAPER]` |
| Exact finite zero-side dictionary | Groskin, *A finite Guinand–Weil dictionary and archimedean tail order...*, arXiv:2607.02828, Theorem 2.5 | `[FINITE_CELL][PAPER]` |
| Displacement singular-value theorem | Beckermann–Townsend, *Bounds on the Singular Values of Matrices with Displacement Structure*, SIAM Review 61 (2019), Theorem 1; arXiv:1609.09494 | `[ABSTRACT][PAPER]` |

## 2. Q1 — the Xi-sample row as a quasi-eigenvector

### 2.1 Exact theorem shape

Let \(m=N\), \(L=\log m\), \(t_{m,n}=2\pi n/L\), and

\[
y_{m,0}=1,\qquad
y_{m,n}=(-1)^n
\frac{\operatorname{centeredXi}(t_{m,n})}
     {\operatorname{centeredXi}(0)} .
\]

Let \(K_m\) be the exact CCM finite matrix in the convention card, put

\[
\nu_m=(K_my_m)_0,
\]

and define the center-normalized residual

\[
\mathcal R_m(y_m)_n
=(K_my_m)_n-y_{m,n}\nu_m .
\]

The registered theorem shape is

\[
\exists C,c>0,\ m_0,\quad
\forall m\ge m_0,\qquad
\|R_m\mathcal R_m(y_m)\|_2
\le C\,10^{-cm}.
\tag{Q1-exp}
\]

That theorem is **not currently proved**. Neither CCM Lemma 7.3 nor the finite Guinand–Weil dictionary has this vector-valued conclusion. `[COFINAL_FAMILY][CONDITIONAL]`

### 2.2 Rate repair forced by the supplied numbers

The label “approximately \(10^{-0.4m}\)” is not the stable scaling visible in the five supplied rows. From those rows,

\[
\frac{-\log_{10}\|R\mathcal R_m(y_m)\|}
     {m/\log m}
=
1.844,\ 2.064,\ 1.960,\ 2.014,\ 2.070.
\]

These values are nearly constant. They are also close to

\[
\frac{\pi^2}{2\log 10}=2.143\ldots .
\]

This is exactly the exponential constant produced by the gamma-factor decay

\[
|\Xi(t)|\lesssim \operatorname{poly}(|t|)\,e^{-\pi|t|/4}
\]

sampled at the first omitted lattice point \(t\sim2\pi m/\log m\). Therefore the source-faithful candidate is not `(Q1-exp)` but

\[
\boxed{
\|R_m\mathcal R_m(y_m)\|_2
\le
C\,m^A
\exp\!\left(-\frac{\pi^2m}{2\log m}\right),
}
\tag{Q1-stretch}
\]

or, before setting \(N=m\),

\[
\|R_{m,N}\mathcal R_{m,N}(y_{m,N})\|_2
\le
C\,m^A N^B
\exp\!\left(-\frac{\pi^2N}{2\log m}\right).
\tag{Q1-general}
\]

This arithmetic diagnoses the likely scale; it does not prove the bound. `[FINITE_CELL][PAPER]`

### 2.3 Exact source mechanism required

A proof should proceed through an infinite-to-finite vector identity, not through a spectral inverse.

First define the two-sided Xi-sample sequence \(y^{(\infty)}\). Then prove an exact global null-row or radical identity for the same source operator,

\[
\mathcal R_{\infty}(y^{(\infty)})=0.
\]

After finite restriction, the residual must become an explicit omitted-tail expression of the form

\[
\mathcal R_{m,N}(y)_n
=
-\sum_{|j|>N}
\bigl(\tau_m(n,j)-y_n\tau_m(0,j)\bigr)y_j,
\tag{VT}
\]

possibly with separately named endpoint terms. The classical decay of \(\Xi(2\pi j/L)\), together with polynomial source-entry bounds, would then yield `(Q1-general)`. `[COFINAL_FAMILY][CONDITIONAL]`

CCM Lemma 7.3 proves convergence of a continuum prolate **trial transform** to \(\Xi\); it does not identify the finite Xi-sample row as a null row of the CCM matrix. The finite Guinand–Weil dictionary identifies a **quadratic value** with a zero sum; even after polarization it does not by itself supply `(VT)` or its stretched-exponential tail estimate. Thus the exact source-locked vector theorem would be new relative to the located statements:

```text
P59_XI_SAMPLE_ROW_AS_PERIODIZED_GLOBAL_NULL_ROW
+
P59_XI_ROW_WEIGHTED_VECTOR_TRUNCATION_RESIDUAL.
```

`[COFINAL_FAMILY][CONDITIONAL]`

## 3. Q2 — what can distinguish the ground row?

Reality, evenness, and the central anchor do not distinguish \(x_m\) from \(y_m\); both already have them. The finite eigen-equation does not distinguish them at the required scale because the relevant operator is nearly singular on a large family of directions. The only plausible selectors are nonlinear or source-specific. `[COFINAL_FAMILY][PAPER]`

### 3.1 Real zeros: best candidate, but bare rigidity is false

The exact ground row has a conditional project theorem placing all zeros of its P59 transform on the real axis. No corresponding theorem is known for the P59 transform built from the Xi-sample row. RH itself would only say that the zeros of \(\Xi\) are real; it would not imply that a finite cardinal/P59 interpolant of samples of \(\Xi\) preserves real-rootedness. `[FINITE_CELL][LEAN]` for the conditional ground bridge; `[COFINAL_FAMILY][CONDITIONAL]` for the Xi row.

Even if both transforms were real-rooted, the generic rigidity claim is false. For \(h>0\) and \(a>0\), define

\[
F_h(z)=\cos(\pi z/h),
\]

\[
G_{h,a}(z)
=
\cos(\pi z/h)
-
a(\pi z/h)\sin(\pi z/h).
\]

Both are even, real entire, of the same exponential type, and normalized to \(1\) at zero. Both have only real zeros: \(G_{h,a}\) is the characteristic function of the nonnegative selfadjoint Robin problem

\[
-u''=\lambda u,\qquad
u'(0)=0,\qquad
u'(1)+a^{-1}u(1)=0.
\]

Yet

\[
F_h(nh)=G_{h,a}(nh)=(-1)^n
\qquad(n\in\mathbb Z),
\]

while \(F_h\not\equiv G_{h,a}\). Therefore even exact agreement on the full Nyquist lattice, plus real zeros, equal type, evenness, and equal anchor, does not identify an entire function. `[ABSTRACT][PAPER]`

The repaired candidate must use the **exact CCM source family**, not the Laguerre–Pólya class alone. Define

\[
\omega_m(\varepsilon)
=
\sup
\left\{
\|R_m(v-y_m)\|_2:
\begin{array}{l}
v_0=1,\ v\ \text{even},\\
\|R_m\mathcal R_m(v)\|_2\le\varepsilon,\\
F_{m,v}\ \text{has the exact source real-zero}\\
\text{or stronger characteristic/interlacing property}
\end{array}
\right\}.
\]

The source-facing target is

\[
\boxed{
\omega_m(\varepsilon_m)
=
O\!\left((\log m)^{-2}\right),
\qquad
\varepsilon_m
=
C m^A e^{-\pi^2m/(2\log m)}.
}
\tag{SEL}
\]

The admissibility predicate in `(SEL)` may use an independently checkable root/interlacing or positive-norming condition. It may not use \(\|R(v-y_m)\|\), the desired convergence, or a complement floor. `[COFINAL_FAMILY][CONDITIONAL]`

**Rank:** 1.  
**Kill-power / first-test cost:** `10/10 · 2/10`.  
**First decisive test:** determine whether the Xi-sample numerator and small-residual perturbations occupy the same real-rooted/characteristic component as the ground numerator. If that admissible component has \(R\)-diameter bounded below, return `P59_REALZERO_CONE_NOT_SELECTIVE`.

### 3.2 Exact minimality: true, but not stable without a modulus

The ground row minimizes the finite Weil Rayleigh quotient exactly. This distinguishes it logically, but not quantitatively in a collapsed spectrum. The exact plant is

\[
K_\varepsilon=
\begin{pmatrix}
0&0\\0&\varepsilon
\end{pmatrix},
\qquad
x=(1,0),\qquad
y=(1,1).
\]

The center-normalized \(x\) is the exact ground minimizer. The residual of \(y\) has size \(\varepsilon\), while \(\|x-y\|=1\). As \(\varepsilon\to0\), exact minimality plus a tiny residual gives no distance bound. `[ABSTRACT][PAPER]`

Minimality becomes useful only after restriction to a nonlinear admissible set such as the source real-rooted characteristic component, followed by a **restricted sharpness modulus**. This is a possible strengthening of `(SEL)`, not a separate linear Ritz route. `[COFINAL_FAMILY][CONDITIONAL]`

**Rank:** 2 jointly with the source real-zero component.  
**Kill-power / first-test cost:** `9/10 · 4/10`.  
**First decisive test:** compute or symbolically characterize the Rayleigh functional on the tangent cone of the source real-rooted component. A flat admissible tangent direction kills the joint selector.

### 3.3 Coefficient sign pattern: cheap to kill, weak as a route

No project theorem supplies

\[
(-1)^n x_{m,n}>0
\]

over the full production carrier. A global one-sign rule is also poorly matched to the target, whose physical samples must eventually follow the oscillatory real function \(\Xi(t)/\Xi(0)\) on expanding intervals. `[COFINAL_FAMILY][CONDITIONAL]`

**Rank:** 3 as a falsifier only.  
**Kill-power / cost:** `8/10 · 1/10`.  
**First decisive test:** an interval-certified sign table for both the ground and target rows beyond the first target sign change. One certified violation closes the global sign pattern.

### 3.4 Alternating curvature: a normality scalar, not a selector

For a fixed nonzero central coordinate, normalized curvature is one affine functional of the remaining coefficient row. Its level set has codimension at most one. It cannot identify one row inside a high-dimensional near-null space. Both the ground row and the Xi-sample row are expected to have bounded curvature on the observed schedule. `[FINITE_CELL][LEAN]` for the finite identity; `[COFINAL_FAMILY][CONDITIONAL]` for any bound.

Curvature remains valuable because it supplies local boundedness of the real-zero ground transforms. It must not be asked to supply Input A by itself.

**Rank:** 4.  
**Kill-power / cost:** `7/10 · 1/10`.  
**First decisive test:** exhibit two center-normalized even near-null rows with the same curvature and nonzero \(R\)-distance; the affine-kernel dimension already predicts this generically.

## 4. Q3 — collapse is not a theorem from displacement rank

Beckermann–Townsend prove the following type of estimate. If

\[
AX-XB=MN^*
\]

has displacement rank \(\nu\), \(A\) and \(B\) are normal, and their spectra lie in sets \(E,F\), then

\[
\sigma_{j+\nu k}(X)
\le
Z_k(E,F)\sigma_j(X).
\]

Rapid decay requires \(E\) and \(F\) to be disjoint and well separated. In the full CCM commutator,

\[
XK-KX=\beta\eta^T-\eta\beta^T,
\]

the left and right displacement operators are the same diagonal node matrix. Hence \(E=F\), the Zolotarev number gives no decay, and the theorem is inert for the full block. `[ABSTRACT][PAPER]`

This is not a technical omission; same-node confluent Loewner structure cannot force any prescribed full singular-value profile. Given distinct nodes \(t_i\) and arbitrary positive numbers \(d_i\), finite Hermite interpolation gives a real polynomial \(f\) satisfying

\[
f(t_i)=0,\qquad f'(t_i)=d_i.
\]

Its confluent same-node Loewner matrix has zero off-diagonal entries and diagonal \(d_i\). Choosing all \(d_i=1\) gives the identity matrix; choosing rapidly decaying \(d_i\) gives any desired diagonal decay. Thus even positive semidefinite same-node Loewner matrices can have arbitrary full spectral behavior. `[ABSTRACT][PAPER]`

The one-set analogue of the Beckermann–Townsend mechanism is blockwise. For disjoint index sets \(I,J\),

\[
X_IK_{I,J}-K_{I,J}X_J
\]

again has small displacement rank. If the node sets \(X_I\) and \(X_J\) are separated, their theorem bounds the singular values of the **off-diagonal block** \(K_{I,J}\). This yields hierarchical/off-diagonal compressibility. It does not imply decay of the full matrix singular values or an upper bound on its smallest eigenvalue. `[FINITE_CELL][PAPER]`

The positive-semidefinite Hankel theorem is also unavailable: the CCM block has not been represented as a PSD Hankel matrix, and that theorem gives a rate of the form

\[
C\rho^{-k/\log n}\|H_n\|_2,
\]

not \(C\rho^{-k}\). `[ABSTRACT][PAPER]`

Therefore

```text
P_COLLAPSE_THEOREM_NOW = REFUTED.
```

A true collapse theorem would need new source mathematics: for example, an analytic-symbol or compact-kernel representation with uniform approximation numbers and exact control of the special diagonal. Displacement rank two alone is not enough. `[COFINAL_FAMILY][CONDITIONAL]`

## 5. Q4 — honest shell status and the moved atom

The universal sentence

```text
no source supplier through the eigen-equation in any representation
```

is too strong. It would also exclude a future nonlinear source theorem that uses the eigen-equation together with real-rooted characteristic data. `[COFINAL_FAMILY][PAPER]`

The exact current conclusion is:

```text
NO_LINEAR_SPECTRAL_STABILITY_SUPPLIER_FROM_CURRENT_EIGEN_EQUATION_REPRESENTATIONS
```

`[COFINAL_FAMILY][PAPER]`

- **H1** has an exact reciprocal-energy identity, but the form evaluates at the collapsed scale and cannot bound the target norm. `[FINITE_CELL][PAPER]`
- **H2** invokes a valid Hardy inequality, but the source supplies no adjacent-mode equation; applying a difference operator creates an uncontrolled dense second divided difference. `[COFINAL_FAMILY][PAPER]`
- **H6** is an abstractly valid projective-transfer route, but every current supplier of its projective defect pays the collapsed gap. `[COFINAL_FAMILY][PAPER]`

The atom therefore moves from “bound \(\Delta\) by a linear stability constant” to the nonlinear identification theorem `(SEL)`:

```text
P59_SOURCE_SPECIFIC_REALZERO_QUASIEIGEN_SELECTOR_MODULUS
```

This does not claim that real zeros are sufficient. The explicit Robin-cosine plant proves that they are not sufficient generically. The theorem must exploit source-specific characteristic/interlacing data or the interaction of that data with exact minimization. `[COFINAL_FAMILY][CONDITIONAL]`

## 6. Ranked next action

### 1. `GOAL058_P59_REALZERO_QUASIEIGEN_SELECTOR_SOURCE_PREFLIGHT`

**Mode:** paper and source, read-only.

The preflight must answer one question before any new computation:

> Does CCM Theorem 5.10 or its source determinant construction give the ground transform a property stronger than `ZerosRealOn`—for example strict interlacing, a fixed characteristic component, or positive norming data—that can be checked on an arbitrary coefficient row?

It must then define \(\omega_m\) without mentioning the unknown ground row in its hypotheses, instantiate the Robin-cosine plant, and design an interval falsifier for the finite admissible-set diameter. `[FINITE_CELL][CONDITIONAL]`

Registered prediction:

```yaml
P_SOURCE_SPECIFIC_REALZERO_COMPONENT_IS_SELECTIVE:
  probability: 0.30
```

Pass:

```text
P59_SOURCE_SPECIFIC_REALZERO_SELECTOR_SURVIVES_PLANTS
```

Fail:

```text
P59_REALZERO_CONE_NOT_SELECTIVE
```

### 2. `P59_POLARIZED_ZERO_SIDE_VECTOR_RESIDUAL`

If the selector preflight fails, polarize the exact finite Guinand–Weil dictionary and seek the vector identity `(VT)`. This route has lower direct selector power but may prove the repaired quasi-eigen residual theorem and expose the exact boundary functional that must be added to the admissibility class. `[COFINAL_FAMILY][CONDITIONAL]`

### 3. `CCM_SOURCE_ANALYTIC_SYMBOL_SINGULAR_VALUE_DECAY`

Treat the observed collapse as a separate side theorem only after an exact analytic-symbol or compact-kernel representation is found. Do not spend more time applying generic displacement-rank bounds to coincident spectral sets. `[COFINAL_FAMILY][CONDITIONAL]`

## FINAL PROPOSAL

Preserve the Curvature–Vitali roof and stop all linear inverse/floor repairs. The new scientific object is the **diameter of the source-admissible real-rooted quasi-eigenspace**, not another spectral gap.

Prove the repaired Xi-row residual rate only as a supporting theorem:

\[
\|R_m\mathcal R_m(y_m)\|_2
\le
C m^A e^{-\pi^2m/(2\log m)}.
\]

Then ask whether every center-normalized source row with residual on that scale and with the full Theorem-5.10 characteristic property must lie within \(O((\log m)^{-2})\) of \(y_m\) in the \(R\)-norm. A positive answer supplies both lattice identification components through the already-built reciprocal-mode shell. A negative finite witness kills the representation early. `[COFINAL_FAMILY][CONDITIONAL]`

## STRONGEST ATTACK

The proposed selector can easily become the desired conclusion under another name. For example,

```text
admissible = real-rooted rows in the same component as the ground row
```

is useless unless “same component” is independently decidable without knowing the ground row or the target distance.

The Robin-cosine plant shows the generic danger at maximum strength: two distinct normalized even real-rooted functions of equal type can agree at every sampling node. Therefore any surviving selector must use a source predicate unavailable to that plant—such as an exact selfadjoint characteristic realization with independently checkable positive norming data—or combine real-rootedness with a restricted sharpness theorem for the exact Weil functional. `[ABSTRACT][PAPER]`

If the source theorem supplies only `ZerosRealOn`, and an interval test finds a second source row at the Xi residual scale with real-rooted P59 transform and nonvanishing \(R\)-distance, issue

```text
P59_REALZERO_CONE_NOT_SELECTIVE
```

and move to the polarized vector-residual route. Do not add curvature, a gap, or the desired distance post hoc.

## CODEX DIRECTIVE

No Codex execution is authorized by this paper-only adjudication.

The next transaction, if separately opened, is:

```text
TASK_ID:
  GOAL058_P59_REALZERO_QUASIEIGEN_SELECTOR_SOURCE_PREFLIGHT

MODE:
  PAPER_AND_SOURCE_READ_ONLY

READ:
  docs/routeB_bus/CONVENTION_CARD_GOAL058.md
  q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59GroundLagrangeZeroSetBridge.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59AlternatingLatticeCurvature.lean
  the pinned CCM Theorem 5.10 source
  docs/routeB_bus/AGENT_REPORT_2026-09-04_GOAL058_RECIPROCAL_MODE_XI_LATTICE_ENERGY_SOURCE_PREFLIGHT.md

RETURN:
  1. the strongest exact source predicate delivered by Theorem 5.10;
  2. an independently checkable definition of omega_m;
  3. the Xi-sample P59/Lagrange numerator;
  4. the Robin-cosine Nyquist plant;
  5. an interval-test contract for the admissible-set diameter;
  6. exactly one code:
       P59_SOURCE_SPECIFIC_REALZERO_SELECTOR_SURVIVES_PLANTS
     or
       P59_REALZERO_CONE_NOT_SELECTIVE.

FORBIDDEN:
  Lean edits;
  numerical runs;
  any full or reduced inverse norm;
  any absolute, relative, or odd-sector floor;
  an admissibility predicate referring to the unknown distance;
  a claim that RH transfers real-rootedness to the finite Xi interpolant;
  Beckermann-Townsend with identical left and right spectral sets.
```

## META CLOSEOUT

- **What became smaller?** The wall is no longer “find a better inverse estimate.” It is one nonlinear modulus \(\omega_m\) measuring whether the exact source real-zero property isolates the Xi row inside the collapsed quasi-eigenspace.
- **What was killed?** Generic real-zero lattice rigidity; minimizer stability without a modulus; curvature as a vector selector; same-node displacement rank as a theorem of full spectral collapse.
- **What must not be tried again?** Reciprocal-energy coercivity, Hardy after the same dense equation, projective Ritz through the collapsed gap, or generic Zolotarev bounds with coincident node spectra.
- **Current smallest named gap:** `P59_SOURCE_SPECIFIC_REALZERO_QUASIEIGEN_SELECTOR_MODULUS`.
- **Next cheapest decisive test:** source-only extraction of the strongest Theorem-5.10 characteristic predicate, armed with the Robin-cosine plant.
- **Fate of prior predictions:** all ten are scored in the machine block without probability edits.
- **Memory entry:** the Xi row is a source-scale quasi-eigenvector, but linear spectral information cannot select it; identification must come from a nonlinear source property or a direct vector explicit-formula identity.

No Lean source was edited. No numerical run was started. No route promotion or RH claim was made.
