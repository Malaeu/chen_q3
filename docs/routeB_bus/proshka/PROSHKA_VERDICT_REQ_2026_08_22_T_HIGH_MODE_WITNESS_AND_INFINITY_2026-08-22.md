# STATUS: PROVED — REQ-T HIGH-MODE WITNESS AND SPECTRUM INFINITUDE RATIFIED
```yaml
PRIMARY: RATIFY_REQ_T_SPHEROIDAL_HIGH_MODE_JACOBI_WITNESS
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-T

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  INPUT_HEAD: 12b4c5bab866630d14b8319eeadf9bc3b9fb6c2f
  QUEUE_PATH: docs/routeB_bus/PROSHKA_QUEUE.md
  QUEUE_BLOB: 733a9e2020cb8c93f8dfbadcd20b37275f4a32a1
  WITNESS_COMMIT: 2b6838fdec73554d553ff422e1a1b50154214d38
  WITNESS_PARENT: 6c73a5dc3a5ee23863c586def80f725e135f9085
  WITNESS_PATH: q3.lean.aristotle/aristotle_input/req_r_ms_satz1_m0_even_spectrum_2026_08_22_harvest/RequestProject/HighMode.lean
  WITNESS_BLOB: 54fe1fd5aba2ed53cef87847695790cb2d36ec96
  DEFS_BLOB: 42df9fba1a6b08efb49f4bb736d40ad8c7054bf8
  SPECTRUM_BLOB: 49fbe8b843837b0f5c310750bbad81875de30fad
  MAIN_BLOB: f5c3f95b4dd009099d17c963c62e16ad400665a0

QUEUE_DISCIPLINE:
  OPEN_REQUESTS_ANSWERED_HERE: [REQ-2026-08-22-T]
  OLDER_OPEN_REQUESTS: []
  QUEUE_STATUS_MUTATED: false

KERNEL_GATE:
  LINUX_REPORTED_FULL_BUILD_JOBS: 8029
  LINUX_REPORTED_BUILD_RESULT: PASS
  LINUX_REPORTED_SORRY: 0
  LINUX_REPORTED_ADMIT: 0
  LINUX_REPORTED_AXIOMS:
    - propext
    - Classical.choice
    - Quot.sound
  JUDGE_RERAN_LAKE_BUILD: false
  SOURCE_AND_PROOF_TERM_AUDIT: PASS

PUBLIC_SURFACE_RATIFIED:
  - hm_exists_row
  - hm_regularEven
  - spheroidal_highMode_eigenvalue_near_specD
  - spheroidal_spectrum_infinite_of_highMode

TARGET:
  CODE: SPHEROIDAL_HIGH_MODE_JACOBI_WITNESS
  STATUS: PROVED
  SCOPE: ABSTRACT
  VERIFIER: LEAN
  EXACT_STATEMENT: >-
    For every fixed real G there exist N : Nat and C : Real with 0 <= C such
    that every n >= N admits a regular even spheroidal eigenvalue Lambda with
    abs (Lambda - specD G n) <= C.
  CONSTANT_OUTSIDE_FORALL_N: true
  EXPLICIT_CONSTANT: 2 * abs G / specRho
  SPECRHO: 1000
  EXACT_TARGET_PREDICATE: RegularEvenSpheroidalEigenvalue

DERIVED_RESULT:
  CODE: SPHEROIDAL_REGULAR_EVEN_SPECTRUM_INFINITE
  STATUS: PROVED
  SCOPE: ABSTRACT
  VERIFIER: LEAN
  PROOF_MECHANISM: high_mode_witnesses_force_unbounded_eigenvalue_set
  INFINITE_INDICES_ALONE_USED_AS_INFINITY: false

SEMANTIC_AUDIT:
  EXACT_SOURCE_OBJECT_PRESERVED: true
  FINITE_MATRIX_SURROGATE_USED: false
  COMPACT_RESOLVENT_ASSUMED: false
  ENDPOINTS_TRIMMED: false
  ODD_BRANCH_SYNTHESIZED: false
  Q3_IMPORTED_IN_SOURCE_PURE_MODULE: false
  POST_HOC_MODE_DEPENDENT_CONSTANT: false
  MOVING_CENTER_DECAY_MISUSED_AS_UNIFORM_IN_N: false
  EXACT_ODE_AND_SHIFT_PRESERVED: true
  EXACT_FLUX_ENDPOINT_CONDITION_PRESERVED: true
  NONTRIVIALITY_PROVED: true
  INFINITUDE_FROM_UNBOUNDED_LAMBDA: true

ARSENAL_AUDIT:
  C04_SAME_COORDINATES_TWO_LAWS: PASS_EXACT_PREDICATE_AND_JACOBI_TO_ODE_CROSSWALK
  C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT: PASS_RHO_THRESHOLD_AND_C_FIXED_BEFORE_FORALL_N
  C10_FUNCTIONAL_NOT_SURROGATE: PASS_INFINITE_SERIES_SOLVES_THE_CONSUMER_PREDICATE

DIRECT_ANSWERS:
  Q1_INDEPENDENT_SEMANTIC_ACCEPTANCE:
    verdict: ACCEPT
    code: RATIFY_HIGH_MODE_WITNESS_AND_INFINITY
  Q2_EVEN_ONLY_PACKAGE:
    verdict: AUTHORIZE_AFTER_MAIN_CLEANUP_GATE
    source_shape: BookRegularEvenSpectrumEven
    full_odd_branch_materialization: forbidden
    mixed_source_DLMF_project_interface_instantiation_now: forbidden
  Q3_QUARANTINED_MAIN_SORRY:
    verdict: REPLACE_IN_SEPARATE_TRANSACTION
    forbidden: false
    statement_change: forbidden
    production_Q3_change: forbidden
    exact_supplier: spheroidal_spectrum_infinite_of_highMode

INTEGRATION_ORDER:
  - discharge_quarantined_Main_spheroidal_spectrum_infinite_sorry
  - build_source_pure_even_only_spectrum_package
  - prove_separate_DLMF_forward_and_project_reverse_crosswalk
  - instantiate_project_interface

CLOSES:
  - SPHEROIDAL_HIGH_MODE_JACOBI_WITNESS
  - SPHEROIDAL_REGULAR_EVEN_SPECTRUM_INFINITY_SOURCE_GAP
  - REQ_S_UNIFORM_HIGH_MODE_EIGENVALUE_WITNESS_DISCRIMINATOR

OPENS: []

CURRENT_SMALLEST_EXECUTABLE_GAP:
  QUARANTINED_MAIN_INFINITY_DEPENDENCY_DISCHARGE
NEXT_LOAD_BEARING_GAP:
  BOOK_REGULAR_EVEN_SPECTRUM_EVEN_SOURCE_PACKAGE
NEXT_PROJECT_SEMANTIC_GAP:
  EVEN_SOURCE_SPECTRUM_TO_DLMF_PROJECT_CROSSWALK

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
GOAL_055: HOLD
ARISTOTLE_FOLLOWUP_AUTHORIZED: false
SECOND_PAID_RUN_NEEDED: false

PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

PREDICTION_SCORE:
  P_R_2_HOLE_FREE_MILESTONE:
    fate: CONFIRMED_PREVIOUSLY
    retroactive_repair: false
  P_R_3_FULL_ENUMERATION_IN_ONE_PAID_RUN:
    fate: REFUTED_AND_REMAINS_REFUTED
    retroactive_repair: false
  P_R_4_FIRST_LOAD_BEARING_FAILURE_EXHAUSTIVE_SPECTRUM:
    fate: CONFIRMED_FOR_PAID_RUN_THEN_REPAIRED_BY_NEW_REPRESENTATION
    retroactive_repair: false
  P_S_R1_HIGH_MODE_WEIGHTED_JACOBI_FIXED_POINT:
    fate: CONFIRMED
    retroactive_repair: false

FAILURE_CODES_FOR_NEXT_TRANSACTION:
  - REQ_T_MAIN_STATEMENT_CHANGED
  - REQ_T_MAIN_IMPORT_CYCLE
  - REQ_T_MAIN_STILL_HAS_SORRYAX
  - REQ_T_MAIN_PULLS_Q3_PROJECT_OBJECTS
  - REQ_T_EVEN_PACKAGE_SYNTHETIC_ODD_BRANCH
  - REQ_T_SOURCE_AND_PROJECT_ADAPTER_MERGED_C04
```

## ROUTE MAP

### 1. The target is the exact source problem

`HighMode.lean` proves a theorem about the same predicate used by the paid
source-pure run:

```lean
RegularEvenSpheroidalEigenvalue G Λ
```

That predicate requires a nonzero even function, continuity on the actual
closed interval, two derivatives on the open interval, the exact shifted
spheroidal equation, and zero endpoint flux.  The high-mode construction feeds
its infinite Legendre series into that literal predicate.  It does not replace
the singular endpoint problem by a trimmed regular interval. `[ABSTRACT][LEAN]`

The differential equation remains

\[
-(1-x^2)f''+2xf'+Gx^2f=(\Lambda+G)f,
\]

which is exactly equivalent to

\[
-\frac d{dx}\bigl((1-x^2)f'\bigr)-G(1-x^2)f=\Lambda f.
\]

Thus the `Λ` versus `Λ+G` discriminator passes. `[ABSTRACT][LEAN]`

### 2. The uniform quantifier is genuine

The fixed-point construction pins the coefficient at the moving mode `n` to
one and solves all other Jacobi rows in weighted deviation coordinates.  Under
one explicit threshold,

\[
8(|G|+1)\rho\le 4n+2-4|G|,
\qquad \rho=1000,
\]

the map sends the half-ball into the quarter-ball and contracts with factor
one half.  Banach's fixed-point theorem gives an exact infinite row.  The
resulting eigenvalue obeys

\[
|\Lambda-\operatorname{specD}(G,n)|
\le \frac{2|G|}{\rho}.
\]

The right-hand constant depends on the fixed parameter `G`, but not on `n`,
and is bound before `∀ n`.  That is exactly the registered discriminator from
REQ-S. `[ABSTRACT][LEAN]`

The conversion from moving-centre decay to origin-centred decay introduces the
factor `ρ^n`.  This factor is not uniform in `n`, but no theorem uses it as a
cofinal constant.  It is consumed only after `n` has been fixed, to justify the
summability, continuity, differentiation and ODE of that one series.  Therefore
there is no hidden finite-to-uniform jump. `[ABSTRACT][LEAN]`

### 3. The row becomes a genuine regular eigenfunction

The exact row equations are passed to the pre-existing infinite-series
machinery in `Spectrum.lean`.  That machinery proves:

```text
series convergence on [-1,1];
termwise first and second derivatives in (-1,1);
the exact spheroidal ODE;
evenness;
continuity up to both endpoints.
```

The new proof then obtains the endpoint flux by multiplying the continuous
first-derivative series by the degenerating factor `1-x²`.  No compact
resolvent, finite truncation or external spectral theorem is assumed.
`[ABSTRACT][LEAN]`

Nontriviality is also real.  At `x=1`, all even Legendre basis functions equal
one.  The centre coefficient is one, while the two-sided geometrically weighted
tail has absolute sum at most `2/999`.  Hence the endpoint value cannot vanish.
`[ABSTRACT][LEAN]`

### 4. Infinitude is not inferred from infinitely many labels

A possible semantic failure would be that many mode indices produce the same
few eigenvalues.  The final theorem does not make that inference.  It assumes
the eigenvalue set finite, takes an upper bound `b`, then chooses `n` so large
that

\[
\operatorname{specD}(G,n)-C>b.
\]

The high-mode theorem supplies an actual member `Λ` of the same eigenvalue set
with `Λ ≥ specD(G,n)-C`, contradicting the upper bound.  Thus the set is
unbounded above and therefore infinite. `[ABSTRACT][LEAN]`

## DIRECT ANSWERS

### Q1 — accept or kill


the result is **accepted**.

\[
\boxed{
\texttt{spheroidal\_highMode\_eigenvalue\_near\_specD}
\text{ and }
\texttt{spheroidal\_spectrum\_infinite\_of\_highMode}
\text{ are ratified.}
}
\]

The proof closes the exact gap selected in REQ-S.  No repair or weakening of
the statement is needed. `[ABSTRACT][LEAN]`

### Q2 — materialize the even-only package?

**Yes, but after one cheaper cleanup transaction.**

The source-pure even-only interface selected in REQ-R remains the correct next
adapter:

```lean
structure BookRegularEvenSpectrumEven (G : ℝ) where
  evenBranch : ℕ → ℝ
  evenBranch_strictMono : StrictMono evenBranch
  evenBranch_regular : ∀ r, RegularEvenSpheroidalEigenvalue G (evenBranch r)
  regular_evenBranch : ∀ Λ,
    RegularEvenSpheroidalEigenvalue G Λ → ∃ r, evenBranch r = Λ
```

Do not rebuild the old full branch and do not invent odd values.  The source
run and all current consumers need only the even spectrum.  A synthetic odd
interpolation would be a `C10` surrogate.

However, the existing `Main.lean` enumeration theorem still inherits
`sorryAx` from its stale local declaration of spectrum infinitude.  Building a
new package from that theorem before replacing the stale dependency would just
transport the old taint into a new wrapper.  Therefore the next executable
transaction is the exact `Main.lean` cleanup below. `[ABSTRACT][CONDITIONAL]`

### Q3 — replace the old `sorry` in `Main.lean`?

**Yes.  It is required, and it must be a separate transaction.**

The quarantine rule prohibited changing `Main.lean` during the proof search.
That search is now complete.  Replacing the one stale proof hole by the new
source-pure theorem does not alter the target, the predicate or the mathematical
object.  It only makes the already harvested strict-enumeration theorem depend
on the proved supplier instead of `sorryAx`.

This transaction must not touch production `Q3`, must not change any theorem
statement, and must not be bundled with the DLMF/project adapter.
`[ABSTRACT][CONDITIONAL]`

## FINAL PROPOSAL

Freeze `HighMode.lean` at blob
`54fe1fd5aba2ed53cef87847695790cb2d36ec96`.

Execute the following order:

```text
1. Main.lean: import HighMode and replace exactly the infinitude sorry.
2. Re-run the source-pure full gate and confirm the final enumeration theorem
   has only the standard axiom triple.
3. Materialize BookRegularEvenSpectrumEven from the cleaned enumeration.
4. Keep DLMF forward membership and project reverse membership in a separate
   crosswalk file.
```

Registered prediction for the next transaction:

```text
P_T_1:
  The Main cleanup is a one-import/one-proof-body transaction and the cleaned
  spheroidal_even_spectrum has exactly
  [propext, Classical.choice, Quot.sound].
  probability: 0.96
```

Likeliest failure point:

```text
IMPORT_CYCLE_OR_NAME_RESOLUTION_ONLY
```

If that occurs, move the high-mode theorem into a lower source module imported
by both `Main.lean` and the adapter.  Do not duplicate the proof and do not
change the theorem statement.

## STRONGEST ATTACK

The strongest reviewer objection is:

> A witness is built for every large index, but the same finite set of
> eigenvalues could be reused forever.

That attack fails because the witness value lies within one fixed distance of
`specD G n`, while `specD G n` tends to positive infinity.  The actual
witnesses are therefore unbounded.  This is stronger than a cardinality count
of the indices.

The second objection is:

> The factor `ρ^n` in the decay crosswalk destroys uniformity.

It would destroy a cofinal analytic estimate, but the proof never uses it for
one.  It uses `ρ^n` only as an existence constant for the fixed row indexed by
`n`.  The only constant required uniformly over high modes is the spectral pin
`2|G|/ρ`, and that constant is independent of `n`.

The third objection is:

> Endpoint flux is a weaker surrogate for source regularity.

For this transaction that is not a new choice: the exact predicate, including
continuity at the real endpoints and zero flux, was source-locked in REQ-R and
used unchanged by the paid harvest.  `HighMode.lean` proves precisely that
predicate.  Any later comparison with a different book convention belongs in
the separate source crosswalk and may not retroactively weaken this result.

## CODEX DIRECTIVE

```yaml
TASK: REQ_T_QUARANTINED_MAIN_INFINITY_DISCHARGE
EXECUTOR: CODEX_OR_LINUX_BODY
MODE: SOURCE_PURE_QUARANTINE_WRITE

BASE_HEAD: 12b4c5bab866630d14b8319eeadf9bc3b9fb6c2f

TOUCH:
  - q3.lean.aristotle/aristotle_input/req_r_ms_satz1_m0_even_spectrum_2026_08_22_harvest/RequestProject/Main.lean
  - docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_T_QUARANTINED_MAIN_INFINITY_DISCHARGE_2026-08-22.md

DO_NOT_TOUCH:
  - q3.lean.aristotle/aristotle_input/req_r_ms_satz1_m0_even_spectrum_2026_08_22_harvest/RequestProject/HighMode.lean
  - q3.lean.aristotle/Q3/**
  - docs/routeB_bus/PROSHKA_QUEUE.md
  - any theorem statement

PATCH:
  - add: import RequestProject.HighMode
  - replace only the proof of spheroidal_spectrum_infinite with:
      exact spheroidal_spectrum_infinite_of_highMode G
  - leave all plants and all other proof bodies unchanged

REQUIRED_SOURCE_RECORD_FIELDS:
  - COMMIT
  - LEAN_PATH
  - LEAN_GIT_BLOB
  - SHA256
  - SOURCE_RECORD_PATH
  - SOURCE_RECORD_BLOB
  - PUBLIC_SURFACE
  - EXPECTED_AXIOM_PROFILES
  - CLOSES
  - OPENS
  - VERIFICATION_HANDOFF
  - NEXT_LOAD_BEARING_GAP

CLOSES:
  - SPHEROIDAL_SPECTRUM_INFINITY_SORRY
  - MS_SATZ1_M0_EVEN_ENUMERATION_SORRYAX
OPENS: []

EXPECTED_AXIOM_PROFILES:
  spheroidal_spectrum_infinite:
    - propext
    - Classical.choice
    - Quot.sound
  spheroidal_even_spectrum:
    - propext
    - Classical.choice
    - Quot.sound

VALIDATION:
  WORKDIR: q3.lean.aristotle
  COMMANDS:
    - lake env lean aristotle_input/req_r_ms_satz1_m0_even_spectrum_2026_08_22_harvest/RequestProject/Main.lean
    - lake build
  REQUIRED:
    - exact command exit codes
    - no sorryAx in either printed theorem
    - no admit
    - standard triple only

SUCCESS:
  CODE: REQ_T_QUARANTINED_MAIN_INFINITY_DISCHARGED
  MEANING: >-
    The harvested source-pure strict enumeration theorem is kernel-clean and no
    longer inherits the paid run's old infinitude hole.

FAILURE:
  CODE: REQ_T_QUARANTINED_MAIN_DISCHARGE_FAILED
  REPORT:
    - exact failing goal or import cycle
    - exact dependency path
    - no fallback theorem and no statement weakening

NEXT_AFTER_GREEN:
  BOOK_REGULAR_EVEN_SPECTRUM_EVEN_SOURCE_PACKAGE
```

## META CLOSEOUT

**What became smaller?**

The source-side wall

```text
regular even spectrum might be finite
```

is gone.  The only remaining taint is a stale dependency in the quarantined
`Main.lean`, not missing mathematics.

**What was killed?**

- the need to assume a compact resolvent;
- the need for a second paid Aristotle run;
- the finite-set shortcut `separated + locally finite ⇒ infinite` remains
  killed by `{0,6}`;
- the possibility that infinitely many mode labels alone prove infinitude;
- the need to synthesize an odd source branch for current consumers.

**What must not be tried again?**

Do not:

```text
reopen the high-mode witness;
introduce a finite Jacobi truncation as the universal spectrum;
assume compact resolvent;
carry rho^n as a uniform cofinal constant;
build the old mixed BookRegularEvenSpectrum directly;
merge source enumeration with the DLMF/project adapter.
```

**Current smallest named gap:**

```text
QUARANTINED_MAIN_INFINITY_DEPENDENCY_DISCHARGE
```

**Next cheapest decisive test:**

Compile `Main.lean` with the new import and print the axiom profiles of both the
infinitude theorem and the final strict enumeration theorem.

**Fate of registered predictions:**

```text
P_R_2: confirmed.
P_R_3: refuted; remains refuted.
P_R_4: confirmed as the paid-run failure class; later repaired by R1, with no
       retroactive change.
R1 high-mode weighted Jacobi fixed point: confirmed.
```

```yaml
iteration:
  target: SPHEROIDAL_HIGH_MODE_JACOBI_WITNESS
  status: PROGRESS
  failed_strategy: separation_plus_local_finiteness_implies_infinity
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: QUARANTINED_MAIN_INFINITY_DEPENDENCY_DISCHARGE
  invariant_learned: a high_mode witness must carry one n_independent spectral pin and solve the exact endpoint predicate
  forbidden_future_move: infer infinitude from labels or import the mixed project adapter before source cleanup
  next_decisive_test: compile cleaned Main and audit final theorem axioms
  progress_class: PROOF_PROGRESS
  route_score: 5
```
