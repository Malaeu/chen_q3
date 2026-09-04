# STATUS: IRREDUCIBLE_ATOM
```yaml
PRIMARY: IRREDUCIBLE_ATOM
PRIMARY_COUNT: 1
OPERATIVE_CODE: FINITE_GROUND_TRANSFORM_TO_CCM_TRIAL_LOCALLY_UNIFORM

REQUEST_ID: REQ-2026-09-04-FULLCHAIN
BOUNDARY_ID: GOAL058_FULL_CLOSURE_CHAIN

REQUEST_LOCK:
  COMMIT: e5dbeb36909fba032bf932b1eaa285931400c8d3
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_FULL_CLOSURE_CHAIN_2026-09-04.txt
  GIT_BLOB: b4a589788118b2c064efb5bad3e6d931e4b96c33
  SHA256: e0af075c863132a686ad7f1b83c86d7e429886c2c3897b004a5a83f5c3399c53
  BYTES: 7966
  LINES: 122
  FINAL_LF: true
  GIT_BLOB_MATCH: true
  SHA256_RECOMPUTED_FROM_FETCHED_UTF8_BYTES: true
  BYTE_COUNT_RECOMPUTED: true
  LINE_COUNT_RECOMPUTED: true

EVIDENCE_BOUNDARY:
  EVIDENCE_CUTOFF: e5dbeb36909fba032bf932b1eaa285931400c8d3
  POST_REQUEST_RESULTS_USED: false
  REVIEW_BOUNDARY: PAPER_ADJUDICATION_ONLY
  LEAN_EDIT_PERFORMED: false
  NUMERICAL_RUN_PERFORMED: false

READJUDICATION:
  OWNER_REQUESTED_SECOND_PASS: true
  PRIOR_VERDICT_BLOB: 1e92ef4825f366f14bfec35a567098f2906216d2
  PRIOR_OPERATIVE_CODE: P59_LADDER_FESHBACH_Y_COMPONENT_O_T_M
  PRIOR_CODE_STATUS: DEMOTED_TO_REPRESENTATION_SPECIFIC_SUBPROBLEM
  CORRECTION_REASON:
    - the prior atom bounds only d2-d2_3
    - the shelf separately leaves d2_3=O(T) unproved
    - a wide admissible schedule need not use the raw 3x3 ladder
    - K8A requires the weakest unchanged consumer interface

OUTPUT_CLASS: IRREDUCIBLE_ATOM
FULL_CHAIN_ON_CURRENT_SHELF: false
BOOKKEEPING_PHASE: CLOSED_BY_ATOM

ATOM:
  NAME: FiniteGroundTransformToCCMTrialLocallyUniform
  CATALOG_STATUS: PLACEHOLDER_MAIN_G3_WALL
  SCOPE: COFINAL_FAMILY
  VERIFIER: CONDITIONAL
  EXACT_QUANTIFIER_FORM: >-
    There exists one precommitted schedule N : Nat -> Nat with N(m) >= m
    whose path i_m=(m,N(m)) is accepted by the production sameCofinalGuard,
    such that, for the exact eta/anchor-normalized Proposition-59 transform
    F_ground(m,N(m)) of the actual finite bottom ground row and the exact
    normalized projected Ferrers-trial transform F_trial(m,N(m)), for every
    compact K contained in the open centered critical strip and every eps>0,
    there exists m0 such that for every m>=m0,
      sup_{z in K} abs(F_ground(m,N(m),z)-F_trial(m,N(m),z)) < eps.
  LEAN_SHAPE: >-
    TendstoLocallyUniformlyOn
      (fun m z => F_ground (m,N m) z - F_trial (m,N m) z)
      (fun _ => 0) atTop centeredCriticalStrip.
  WEAKEST_SOURCE_RATE_INTERFACE: >-
    For every compact K, the exact P59 compact-evaluation norm of the
    bottom-spectral-complement component of the source trial, including the
    literal phase/anchor normalization correction, tends to zero on the same
    schedule. No free error function or free compact-rate premise is allowed.
  MINIMAL_MISSING_IDENTITY: >-
    A source-defined factorization
      F_ground - F_trial = E_source
    on the same finite carrier and normalization, together with a bound
      sup_K |E_source| <= epsilon_m(K), epsilon_m(K)->0,
    where E_source is computed from K_{m,N}, its bottom spectral projector,
    and the literal Ferrers trial before any inverse-gap operator-norm bound.
  EXACT_REFUTER: >-
    A compact K, eps>0, and a cofinal subsequence m_j for every admissible
    precommitted schedule under test such that
      sup_K |F_ground(m_j,N(m_j))-F_trial(m_j,N(m_j))| >= eps.
    Finite caches alone cannot refute the existential cofinal theorem.
  CACHE_DISCRIMINATOR: >-
    On K0={z: |Re z|<=1, |Im z|<=1/4}, compute the anchored P59 difference
    directly from the cached ground and trial rows at (13,13),(23,23),
    (43,43),(83,83),(13,120). Pre-register COMPACT_DEFECT_NONDECAY if the
    precision-stable values at N=m obey E_43>=0.90*E_23 and
    E_83>=0.90*E_43. This kills the N=m compact-decay representation only,
    not the existential schedule atom.

WHY_NOT_PRIOR_ATOM:
  EXACT_IDENTITY: d2 = d2_3 + inner(e0,p-z2_3)
  MISSING_RATE_1: abs(d2_3) <= C0*T
  MISSING_RATE_2: abs(inner(e0,p-z2_3)) <= C1*T
  SHELF_PROVES_RATE_1: false
  SHELF_PROVES_RATE_2: false
  CONSEQUENCE: >-
    Proving only the Feshbach y-component rate does not prove d2=O(T), hence
    it does not close the requested chain. The D2 shelf explicitly records
    P59_COMPRESSED_SECOND_RITZ_VECTOR_ASYMPTOTIC as a second failure point.
  FESHBACH_ATOM_RETAINED_AS: CANDIDATE_REPRESENTATION
  CURVATURE_E_M_RETAINED_AS: CANDIDATE_REPRESENTATION

SCHEDULE_AUDIT:
  N_EQUALS_M: ONE_REPRESENTATION_NOT_A_THEOREM
  WIDE_13_120: STRONG_FINITE_EVIDENCE
  WIDE_FULL_CHAIN_ON_REQUEST_SHELF: false
  WIDE_MISSING_SUPPLIER: >-
    A source-specific cofinal saturation/projective-rate theorem for a
    precommitted roof-admissible N(m); sameCofinalGuard bookkeeping alone
    supplies no spectral rate.
  SECOND_WIDE_CELL_AT_REQUEST_CUTOFF: UNSATURATED_AND_INSTRUMENT_FLOORED
  HARDNESS_REMOVED_BY_SCHEDULE_CHANGE: false
  HARDNESS_MOVED_TO_FEWER_HIDING_PLACES: plausible_not_proved

CANDIDATE_REPRESENTATIONS:
  R1_SECOND_MODE_FULL_OVERLAP:
    target: P59_SECOND_MODE_OVERLAP_O_L_MINUS_2
    requirement: >-
      Bound the full multiplicity-safe second-even spectral projection of
      the Xi row, not only one Feshbach summand, and control the combined
      higher-mode/profile remainder needed by the compact consumer.
    kill_power: 9/10
    estimated_cost: 8/10
  R2_CURVATURE_TRANSFER:
    target: >-
      Use 2*pi*d2=ell1*(alpha*M-E), but solve the identity noncircularly:
      control the transfer denominator/moment and the full ground-side
      remainder without assuming alpha=O(T), which is rate-equivalent to d2.
    kill_power: 9/10
    estimated_cost: 7/10
  R3_WIDE_SCHEDULE_PROJECTIVE_RATE:
    target: >-
      Precommit N(m), prove sameCofinalGuard and a source-specific cofinal
      Rayleigh-saturation/complement-gap estimate whose compact evaluation
      product tends to zero.
    kill_power: 10/10
    estimated_cost: 9/10

OBSERVER_PREDICTION_FATES:
  P_JUDGE_RETURNS_IRREDUCIBLE_ATOM_0_70: CONFIRMED
  P_ATOM_IS_FESHBACH_Y_COMPONENT_OR_E_M_0_55: >-
    REFUTED_AS_THE_OPERATIVE_ATOM; CONFIRMED_ONLY_AS_TWO_REPRESENTATIONS
  P_JUDGE_BUILDS_CHAIN_ON_WIDE_SCHEDULE_0_30: REFUTED_AT_REQUEST_CUTOFF
  P_CHAIN_HAS_ZERO_NEW_MATH_STEPS_0_10: REFUTED

JUDGE_K6_REGISTER:
  P_FULL_CHAIN_EXISTS_ON_CURRENT_SHELF: 0.03
  P_ATOM_IS_NEW_MATH_BEYOND_CCM_SECTION_7_LEMMA_7_2_7_3: 0.97
  P_SCHEDULE_CHANGE_MOVES_WALL_TO_FEWER_HIDING_PLACES: 0.72

K8A:
  DOWNSTREAM_CONSUMER: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  ACTUAL_CONSUMER_REQUIREMENT: >-
    The same normalized finite-ground family converges locally uniformly to
    centeredXi after the already separated trial-to-Xi leg.
  ORIGINAL_REQUESTED_OBJECT: abs(d2_m)<=C*T_m cofinally
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACE: FiniteGroundTransformToCCMTrialLocallyUniform
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: source-specific cofinal bottom-spectral selection in compact P59 norm

CLOSES:
  - FULLCHAIN_BOOKKEEPING_SEARCH
OPENS: []

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## ROUTE MAP

### S1 — exact finite P59 second-jet dictionary

**(a) Statement.** For every `L>0`, `N`, and even real rows `v,q` with
`v(0)q(0)≠0`,
\[
 \kappa(F_v)-\kappa(F_q)
 =\frac{L^2}{2\pi^2}\sum_{k=1}^{N}
   \frac{v_k/v_0-q_k/q_0}{k^2}.
\]

**(b) Type.** `THEOREM`:
`q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59GroundTrialSecondJetDifference.lean`,
Git blob `7cbd0dc6742266e2193e25f22fc4146f47da65a7`,
theorem `proposition59_ground_trial_second_jet_difference_real`.

**(c) Inputs.** Exact Proposition-59 value and second derivative at zero.

**(d) K3 cargo.** Preserves the finite carrier, coordinate
`-Lz/(2π)`, evenness and centre normalization. Drops all spectral selection,
compact topology and cofinal-rate information.

**(e) FIRST_FAILURE.** An equality of second jets does not control the whole
function on any compact and supplies no bound on its right-hand side.

**(f) Discriminator.** Recompute both sides with certified intervals.
Pre-registered failure number: relative residual `>10^-30` is
`SECOND_JET_OBJECT_OR_NORMALIZATION_MISMATCH`.

### S2 — exact ladder/Feshbach block algebra

**(a) Statement.** For every finite symmetric `K`, orthonormal ladder synthesis
`B`, and exact eigenpair `Ku=λu`, with `p=Bᵀu` and `r=Qu`,
\[
 (A-\lambda I)p+Cr=0,\qquad
 C^\mathsf Tp+(D-\lambda I)r=0.
\]
Under the exact complement inverse,
\[
 r=-(D-\lambda I)^{-1}C^\mathsf Tp,\qquad
 [A-C(D-\lambda I)^{-1}C^\mathsf T]p=\lambda p.
\]

**(b) Type.** `THEOREM`:
`q3.lean.aristotle/Q3/Proofs/RouteB/P59XiLadderFeshbachRemainder.lean`,
Git blob `96a7b56eaa4377a890847df6b8dac40dc7046933`.

**(c) Inputs.** The source finite CCM matrix, its exact eigenpair and an
orthonormal source-defined ladder.

**(d) K3 cargo.** Preserves the full complement feedback and finite carrier.
Drops no modes. It does not identify the true in-ladder vector with a raw Ritz
vector and supplies no estimate on the inverse or its scalar component.

**(e) FIRST_FAILURE.** Any generic operator-norm estimate pays the inverse
complement gap. The shelf contains no source cancellation removing that scale.

**(f) Discriminator.** Check the two projected equations and the reconstructed
Feshbach equation. Pre-registered failure number: normalized residual
`>10^-30` is `FESHBACH_OBJECT_OR_ORIENTATION_MISMATCH`.

### S3 — audit of the proposed `d₂` reduction

**(a) Statement.**
\[
 d_{2,m,N}
 =d^{(3)}_{2,m,N}
 +\langle e_0,p_{m,N}-z^{(3)}_{2,m,N}\rangle .
\]

**(b) Type.** `THEOREM` for the equality; both asymptotic bounds below are
`NEW-MATH`:
\[
 |d^{(3)}_{2,m,N(m)}|\le C_0T_{m,N(m)},\qquad
 |\langle e_0,p-z^{(3)}_2\rangle|\le C_1T_{m,N(m)}.
\]

**(c) Inputs.** S2, coherent second-mode selection or its spectral-projection
replacement, and the exact Xi-polynomial ladder.

**(d) K3 cargo.** Preserves the exact scalar overlap and separates raw
compression from complement feedback. It drops neither term; deleting either
one is a false proof.

**(e) FIRST_FAILURE.** The previous verdict promoted only the second bound.
The first is separately unproved on the shelf. Hence that atom was not
consumer-sufficient.

**(f) Discriminator.** Compute
`D_m=|d2_3|/T` and `R_m=|d2-d2_3|/T`.
Pre-register `TWO_RATE_FAILURE` if either ratio at `m=83` is at least
`1.25` times its value at `m=43`, with coherent orientation and precision
stability. This rejects the frozen decomposition, not the cofinal theorem.

### S4 — unchanged consumer interface

**(a) Statement.** `ATOM.EXACT_QUANTIFIER_FORM`.

**(b) Type.** `NEW-MATH`:
`FiniteGroundTransformToCCMTrialLocallyUniform`.

**(c) Inputs.** The exact source bottom-ground transform and projected Ferrers
trial transform on one common schedule. S1–S3 may be used, but are not mandatory
and do not define the atom.

**(d) K3 cargo.** Carries the same source object, anchor normalization, finite
carrier, coordinate, topology and cofinal path into the downstream trial-to-Xi
limit. It drops no mode and introduces no post-hoc schedule.

**(e) FIRST_FAILURE.** The shelf contains identities and finite diagnostics,
but no source-specific cofinal estimate in the compact P59 norm. Reordering
identities cannot manufacture a limit.

**(f) Discriminator.** `ATOM.CACHE_DISCRIMINATOR`. Exact refutation requires
`ATOM.EXACT_REFUTER`.

## IRREDUCIBLE_ATOM

**IRREDUCIBLE_ATOM — `FiniteGroundTransformToCCMTrialLocallyUniform`.**

The former `P59_LADDER_FESHBACH_Y_COMPONENT_O_T_M` is retained as one possible
mechanism, not as the irreducible atom. It is too narrow: even a proof of that
rate leaves the raw compressed second-coordinate rate unproved, and a wide
schedule can attack the unchanged consumer without using the frozen 3×3 ladder.

## FINAL PROPOSAL

Close the bookkeeping phase at the unchanged G3 consumer. Do not write another
wrapper and do not declare either `d₂=O(T)` or the Feshbach subterm necessary.

The cheapest belief-changing test is the direct compact P59 ground/trial
difference on `K0` from the already cached rows. It tests what the roof consumes,
not a proxy. If it rejects `N=m`, compare the same functional at `(13,120)`; this
classifies whether width removes finite truncation error. It still cannot certify
a cofinal wide schedule.

Future mechanism work must choose one registered representation above. The
current preference is R1 only if it attacks the **full** second-mode projection;
otherwise R2 is cleaner than a raw inverse-gap Feshbach estimate.

## STRONGEST ATTACK

A reviewer can object that `FiniteGroundTransformToCCMTrialLocallyUniform` is a
wall name, not an indivisible theorem. Correct: “irreducible” here is relative
to the frozen shelf. The point is not that no finer decomposition exists. The
point is that every surviving decomposition needs a new source-specific
cofinal estimate, while the shelf supplies only exact identities.

The stronger objection is the saturated cell `(13,120)`. It shows the atom may
be easy on a wide schedule. It does not put the theorem on the shelf: one cell
does not provide `sameCofinalGuard`, a cofinal saturation law, or a compact
evaluation rate. The second wide cell in the request is explicitly unsaturated
and instrument-limited.

## META CLOSEOUT

- **What became smaller?** The target is the exact G3 compact consumer, with
  all representation-specific subterms demoted below it.
- **What was killed?** The claim that the Feshbach y-component alone is the
  single sufficient atom.
- **What must not be tried again?** Proving only one summand of `d₂`; treating
  a finite wide cell as a cofinal law; generic inverse-gap operator norms.
- **Current smallest named gap?**
  `FiniteGroundTransformToCCMTrialLocallyUniform`.
- **Next cheapest decisive test?** Direct compact P59 error on `K0`, using
  existing cached ground/trial rows and the registered `0.90` nondecay rule.
- **Prior predictions?** Scored in the YAML without retroactive repair.
- **Memory entry?**
```yaml
iteration:
  target: REQ-2026-09-04-FULLCHAIN
  status: PROGRESS
  failed_strategy: representation-specific Feshbach subterm promoted as atom
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: FiniteGroundTransformToCCMTrialLocallyUniform
  invariant_learned: atom must be sufficient for the unchanged consumer across admissible schedules
  forbidden_future_move: close only one decomposition summand and call the wall closed
  next_decisive_test: direct compact P59 ground/trial error ledger on K0
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
