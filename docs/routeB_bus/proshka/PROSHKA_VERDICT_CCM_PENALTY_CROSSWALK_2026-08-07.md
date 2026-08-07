# STATUS: OPEN — MOVE 1 RATIFIED WITH A SOURCE-LOCK PRE-GATE; GAP AND NORMALIZATION SPECIFICATIONS REPAIRED

```yaml
PRIMARY: RUN_CCM_PENALTY_CROSSWALK_BETA_DELTA_PROFILE
PRIMARY_COUNT: 1
OPERATIVE_CLASS: RUN_CCM_PENALTY_CROSSWALK_BETA_DELTA_PROFILE

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  PIN: fa038f59451da81c82f94da4234d22b66d6214fd
  ORIGIN_HEAD_EQUALS_PIN: true
  RECON_PRESENT: true
  PACKET_PRESENT: true

R6:
  MOVE_1: RATIFIED_WITH_MANDATORY_PREFLIGHT
  SIEG_OF_PENALTY_BEFORE_RUN: REJECTED
  FINITE_CCM_RUN: AUTHORIZED_MATHEMATICALLY
  CLAIMS_SLOT_H2A: false
  CLAIMS_ALL_LAMBDA_INPUT_A: false

R7:
  DELTA_057_2:
    retain: true
    new_role: SECTIONAL_GAP_RATE_DIAGNOSTIC
    decisive_for_operator_transfer: false
  BETA_N_PROFILE:
    add: true
    role: FORM_CERTIFICATE_TRANSFER_DISCRIMINATOR
    fixed_lambda: true
    fixed_embedded_probe_q: required
  RATE_COORDINATE:
    primary: effective_slope_of_log_Delta_against_lambda_squared
    also_record:
      - actual_trial_numerator_rate
      - prolate_leakage_proxy_rate
      - log_ratio_numerator_over_Delta

R8:
  OLD_BINARY_P_DELTA: KILLED_AS_MISSPECIFIED
  PROPOSED_TERNARY_P_DELTA: REPAIRED_AS_NONEXHAUSTIVE
  CLOSED_RATE_CLASSES:
    - DELTA_SUBEXPONENTIAL_IN_LAMBDA_SQUARED
    - DELTA_EXPONENTIAL_SUBCRITICAL_TO_NUMERATOR
    - DELTA_CRITICAL_SAME_EXPONENTIAL_RATE
    - DELTA_SUPERCRITICAL_FASTER_THAN_NUMERATOR
    - DELTA_RATE_UNRESOLVED

R9:
  INDEX_CROSSWALK:
    status: REQUIRED
    architecture: SEPARATE_LOGICAL_OBJECT
    execution: PHASE_ZERO_OF_SAME_OPERATIONAL_BATCH
    numerical_run_before_pass: forbidden

R10:
  NORMALIZATION:
    status: DUAL_NORMALIZATION_LOCK_REQUIRED
    penalty_probe: G_UNIT_NORMALIZATION
    theorem510_ground_vector: DELTA_N_ANCHOR_NORMALIZATION
    these_are_the_same_normalization: false
    delta_N_is_an_L2_norm: false

SOURCE_CORRECTION:
  PROLATE_DEFICIT_RATE:
    object: one_minus_chi_2
    paper_status: VERIFIED
    scale: lambda_power_times_exp_minus_4pi_lambda_squared
  TRUE_INPUT_B_NUMERATOR_RATE:
    status: OPEN_BRIDGE
    may_be_replaced_by_prolate_rate_without_theorem: false

DIRECT_CONSUMER:
  Q3.RouteB.H2aPenalty.H2a_SimpleEvenGround_FromPenaltyCoercivity

RUNNER_UP_NOT_AUTHORIZED:
  CCM_SIEG_of_penalty

STOP: CCM_PENALTY_SOURCE_LOCK_OR_PROFILE_UNCLASSIFIED
SUCCESS: CCM_PENALTY_SOURCE_LOCK_AND_RATE_PROFILE_CLASSIFIED

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C12_BOUNDED_POTENTIAL_EXCLUSION

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: UNIT_AUDIT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ARISTOTLE_SUBMISSION: NONE
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

## 1. Source audit

The branch head is exactly `fa038f59451da81c82f94da4234d22b66d6214fd`. The commit contains
the stated reconstruction, the revised packet, the `R6–R10` questions, and the explicit
boundary between disk-verified facts and Mythos relay. `[ABSTRACT][PAPER]`

The two facts you independently verified are correct:

1. The project theorem `V_n_m_orthonormal` proves orthonormality of the literal production
   modes in `H_m = L²(I_m, d*u)`, so the Gram matrix of any finite mode restriction is the
   identity. `[FINITE_CELL][LEAN]`

2. `integral_comp_logWindow_dStar` proves the exact transport `x = log(lambda_m u)`,
   `d*u ↦ dx`, and the project has `L_m = log m = 2 log √m`. Thus the exact parameter
   crosswalk is `λ² = m`. `[ABSTRACT][LEAN]`

I also independently checked the previously relayed parts against the primary CCM paper. It
explicitly gives: the orthonormal basis `V_n = κ(U_n)`; the real symmetric truncated Weil
matrix; the rank-two `W_{0,2}` contribution; the finite von-Mangoldt sum through
`k ≤ e^L = λ²`; the archimedean contribution; the reversal involution `γ(V_j) = V_{−j}`;
`Tγ = γT`; the exact definition of "even-simple". `[FINITE_CELL][PAPER]`

The paper also proves that the full Fourier-mode span is a form core for `QW_λ`, and that the
lowest finite-section eigenvalue converges to the operator's lower bound. This supports the
form-core route, but it does not transfer a finite spectral gap by itself.
`[COFINAL_FAMILY][PAPER]`

Therefore the reconstruction's epistemic status can be strengthened:

```text
G = I:                                    independently verified.
κ / λ²=m transport:                       independently verified.
K real symmetric, explicit components:    independently verified from primary source.
J=γ and JK=KJ:                            independently verified from primary source.
even-simple definition:                   independently verified from primary source.
uniform penalty floor and true operator gap:  still open.
```

## 2. R6 — ratify Move 1, do not wait for `SIEG_of_penalty`

**Decision: `RUN_CCM_PENALTY_CROSSWALK_BETA_DELTA_PROFILE`.** Move 1 is ratified as a bounded
scientific transaction. It should run **before** `SIEG_of_penalty`.

The reason is structural. `SIEG_of_penalty` is a downstream family-to-roof adapter. It would
transport concrete finite data satisfying the eight hypotheses of
`H2a_SimpleEvenGround_FromPenaltyCoercivity` into the Route-B `SIEG` predicate. It cannot
tell us whether the CCM matrices admit such data or whether a useful penalty certificate
exists. The source file itself describes `SIEG_of_penalty` as the still-unwritten family
instantiation after the finite engine. `[ABSTRACT][LEAN]`

The finite engine is already exact: `K − βG + τ(Gq)(Gq)* ⪰ 0`, `q*Gq = 1`, `a = q*Kq < β`
implies existence of the lowest generalized eigenvalue, simplicity, `J`-evenness, and a gap
at least `β − a`. `[FINITE_CELL][LEAN]`

### Exact scope of a green result

A green interval or exact-rational certificate at one `(λ, N)` would prove a genuine theorem
about that **finite CCM truncation** after source crosswalk and Lean import: the CCM finite
ground state is simple, even, isolated, with a certified finite gap.

It would **not** yet prove: `SlotH2a` for the existing Q3 canonical family; input A for all
`λ`; a uniform operator gap; ground-to-trial tracking; RH. `[FINITE_CELL][CONDITIONAL]`

So the correct progress label is **finite CCM input-A certificate, not project SlotH2a
closure**.

Failure to find a certificate also does not prove that the CCM ground state is not simple or
even. The penalty condition is sufficient, not necessary.

## 3. R7 — keep both probes, but assign them different jobs

### 3.1 Reclassify 057.2

Keep the sectional gap `Δ_N(λ) = λ₂^{(N)}(λ) − λ₁^{(N)}(λ)`, but rename its role to
`SECTIONAL_GAP_RATE_DIAGNOSTIC`. It is useful for input-B scale diagnostics. It is **not** the
decisive test for transfer to the continuum operator.

Galerkin restriction gives upper bounds to each ordered eigenvalue: `λ_k^{(N)} ↓ λ_k`. That
does not provide a lower bound for the true `λ₂`. Hence a wide finite-section gap does not
imply a wide operator gap. The repository's zoom document gets this distinction right.
`[COFINAL_FAMILY][PAPER]`

### 3.2 Log the rate, not just "small"

Let `x = λ²`. For two adjacent sampled cutoffs record the local effective slope

```
σ_{Δ,N}(x₁,x₂) := −[log Δ_N(x₂) − log Δ_N(x₁)] / (x₂ − x₁)
```

and the cumulative effective rate `r_{Δ,N}(x) := −log Δ_N(x) / x`.

A fixed `N = 120` profile is a **control experiment, not asymptotic evidence**. For every
sampled `λ`, the run must also contain an `N`-ladder and demonstrate numerical stabilization
before that `λ`-value enters the slope fit.

### 3.3 Add the `β_N` profile

At fixed `λ`, define the maximum certifiable floor for a **fixed probe** `q`:

```
β*_N(λ,q) := sup{ β > a : ∃τ ≥ 0, K_N − βI + τqq* ⪰ 0 },    G = I,  a = q*K_N q
```

The quantity that matters is `g_N(λ,q) = β*_N(λ,q) − a`. This is the correct finite
diagnostic for whether a dimension-independent form floor may exist.

But the probe must be fixed across the `N`-ladder:

1. Choose `q` in one precommitted `E_{N₀}`.
2. Embed that same vector by **zero-padding** into every `E_N`, `N ≥ N₀`.
3. Do **not** recompute a better `q_N` at every dimension for the transfer channel.

If `q_N` is reoptimized at every `N`, stabilization of `β*_N − a_N` does not certify one form
inequality on a common core. It only reports a sequence of unrelated finite witnesses. This is
a **C09** precommit issue.

A second `q_N = P_N k_λ/‖P_N k_λ‖` channel may be logged as a performance diagnostic, but it
must be labeled `MOVING_PROBE_DIAGNOSTIC — NOT_TRANSFER_EVIDENCE`.

### 3.4 Relative numerator channel

Record three rates separately: `σ_Δ` (gap), `σ_num` (actual trial residual / input-B
numerator), `σ_prolate` (prolate leakage proxy). The decisive ratio is governed by
`log(numerator/Δ) = log(numerator) − log Δ`, not by `log Δ` alone.

## 4. R8 — the binary split dies, but the proposed ternary split is still incomplete

The old binary `P-Δ = 0.6` is killed as misspecified. The proposed three cases are an
improvement, but they omit a real fourth possibility: the gap can decay **faster** than the
numerator. They also omit an unresolved-rate outcome when slopes do not stabilize or fall
below the instrument floor.

The closed classification must be:

| Code | Effective behavior | Input-B interpretation |
|---|---|---|
| `DELTA_SUBEXPONENTIAL_IN_LAMBDA_SQUARED` | `σ_Δ → 0` | B remains viable |
| `DELTA_EXPONENTIAL_SUBCRITICAL_TO_NUMERATOR` | `0 < σ_Δ < σ_num` | B remains viable, reduced exponent |
| `DELTA_CRITICAL_SAME_EXPONENTIAL_RATE` | `σ_Δ = σ_num` | polynomial powers and constants decide |
| `DELTA_SUPERCRITICAL_FASTER_THAN_NUMERATOR` | `σ_Δ > σ_num` | this residual/gap implementation of B fails |
| `DELTA_RATE_UNRESOLVED` | unstable slope, insufficient range, or precision floor | no mathematical verdict |

`[COFINAL_FAMILY][CONDITIONAL]`

### Important source correction

The exact asymptotic `1 − χ₂(λ) ~ C·λ⁹·e^{−4πλ²}` is attached to the **prolate concentration
deficit**. The source then reports a striking numerical similarity between that quantity and
the smallest Weil eigenvalue. It does **not** prove that the actual input-B residual numerator
equals that prolate deficit. `[COFINAL_FAMILY][PAPER]`

Groskin's high-precision results supply strong finite numerical evidence for extremely small
Weil eigenvalues, but explicitly do not prove the asymptotic bridge or RH. `[FINITE_CELL][PAPER]`

Therefore the packet sentence *"the numerator has scale exp(−4πλ²)"* must be weakened to:
*"the prolate leakage proxy has a paper-supported `λ⁹exp(−4πλ²)` scale; the actual input-B
numerator rate remains an open source-target bridge."* Treating the proxy as the actual
numerator would be a **C04/C10** category error.

### Registered replacement prediction

```text
P-DELTA-R:
  the effective sectional gap rate will be subcritical
  relative to the actual trial-numerator rate after N-stabilization.
```

No probability is assigned. Its fate must be scored exactly after the profile. The old binary
prediction is **not** scored as confirmed or refuted; it was not a valid exhaustive event
partition and was replaced before the test.

## 5. R9 — separate logical object, same operational batch

The apparent "single versus double index" mismatch is mostly notation, but it still needs a
theorem-grade crosswalk. In the paper `λ` is an external parameter suppressed in the symbol
`V_n`; `N` is the finite truncation parameter; `n ∈ [−N,N]` indexes basis vectors. In the
project `PairIndex` packages the two external parameters: `i.m ↔ λ²`, `i.N ↔ N`,
`n ↔ basis mode`. `[FINITE_CELL][PAPER]`

**Decision.** The crosswalk is a **separate logical transaction/object**, and a **mandatory
Phase 0** of the same operational Move-1 batch. It must pass before any matrix numerics are
interpreted. Call it `CCM_D0_MODE_INDEX_CROSSWALK`.

Its exact contract: `λ = √(i.m)`, `L = 2 log λ = log(i.m) = L_m(i)`, `N = i.N`, and for every
`n ∈ [−N,N]`, `V_n^{CCM,λ} = V_{n,m}^{Q3}(i,n)` after the already proved logarithmic
transport.

It must also lock: basis order `−N, −N+1, …, N`; `G = I`; `J_{n,r} = 1_{n=−r}`; the
sign/orientation `K = W_{0,2} − W_ℝ − Σ_p W_p`; the paper prime cutoff `k ≤ e^L = λ² = i.m`.

This object should remain independently reusable by `CCM_SIEG_of_penalty`,
`FiniteQWTheorem510RealZeroBridge`, and future matrix-entry crosschecks. It must **not** be
hidden as a comment inside a numerical script.

## 6. R10 — the two normalizations are not the same

This requires a direct correction. The paper's condition `δ_N(ξ) = 1` is **not** an
`L²`-normalization. The paper identifies it with the linear anchor `⟨η, ξ⟩ = 1`, where
`η = Σ_{j=−N}^{N} V_j`, up to the stated `L^{−1/2}` Dirichlet-kernel factor. It separately
uses the orthonormality of the basis. `[FINITE_CELL][PAPER]`

By contrast `q*Gq = 1` is exactly a Hilbert or `G`-norm condition. With `G = I` it is
`‖q‖₂ = 1`. **These remain different when `G = I`.**

### Mandatory dual-normalization lock

**Penalty probe.** Let `q_raw` be the precommitted prolate trial vector, constructed without
diagonalizing `K`. Define `q_unit = q_raw/‖q_raw‖₂`. Use **only** `q_unit` in `q*q = 1`,
`a = q*Kq`, `K − βI + τqq* ⪰ 0`.

**Theorem-5.10 ground vector.** After simplicity and evenness have been proved, choose a
nonzero ground eigenvector `ξ_unit`, prove separately `δ_N(ξ_unit) ≠ 0`, and define
`ξ_δ = ξ_unit/δ_N(ξ_unit)`. Then `δ_N(ξ_δ) = 1`. The rescaling does not change the
eigenspace, eigenvalue, or parity. It does change the representative.

**Forbidden:** use `δ_N`-normalized `ξ` as though it automatically satisfies `q*q = 1`; use
the numerically computed ground vector as the precommitted `q`; set `q` equal to `ξ` after
looking at the spectrum. The last move would destroy the certificate's role as an
independently constructed trial and violate **C09**.

## 7. K6 object precommit for Move 1

```text
Control point:
  λ² = m = 13
  initial public-control truncation N = 120

Coordinates:
  λ = √13 · L = log 13 · modes n = −N..N · G = I · J(V_n) = V_−n

Matrix orientation:
  K = W_0,2 − W_R − W_prime

Probe:
  q_raw = finite coefficients of the source prolate trial k_λ
  q_unit = q_raw / ||q_raw||₂
  q must be constructed BEFORE the K-spectrum is inspected

Penalty data:
  a = q_unit* K q_unit · β > a · τ ≥ 0

Theorem-5.10 normalization:
  separate and downstream; δ_N(ξ)=1 is NOT used to normalize q

Rate channels:
  Δ_N · β*_N − a · actual trial numerator · prolate leakage proxy

Precision:
  arbitrary precision; precision-doubling stability required; no float64 route decision
```

The implementation package may generate matrix values, but the **primary paper formulas are
authoritative**. At least one diagonal entry, one off-diagonal entry, the prime cutoff, matrix
symmetry, and `JK = KJ` must be independently reconstructed before the implementation is
trusted.

## 8. Load-bearing plants

| id | mutation | required result |
|---|---|---|
| `P-R6-1` index/length | `λ = m` or `L = log λ` instead of `λ = √m`, `L = log m` | `CCM_D0_INDEX_LENGTH_CROSSWALK_MISMATCH` |
| `P-R6-2` prime sign | `K = W_{0,2} − W_ℝ + Σ_p W_p` | `CCM_WEIL_MATRIX_ORIENTATION_MISMATCH` |
| `P-R6-3` normalization collision | replace `q_unit` by a vector normalized only through `δ_N(q) = 1` | `CCM_PENALTY_PROBE_NOT_G_UNIT` |
| `P-R6-4` moving-probe transfer fraud | recompute the optimizer `q_N` independently at every `N`, then claim stabilization proves a common-core inequality | `CCM_BETA_N_MOVING_PROBE_NOT_TRANSFER_EVIDENCE` |
| `P-R6-5` prolate proxy substitution | replace the actual trial residual/numerator by `1 − χ₂` without an equality or one-sided bridge | `CCM_PROLATE_PROXY_AS_INPUT_B_NUMERATOR` |

These plants mutate independent semantics: parameter indexing, Weil sign, norm convention,
common-core quantifier, and source-target object identity.

## 9. Strongest attack

A green run can still certify the wrong statement in three ways:

1. **Wrong family** — the CCM finite truncation is not automatically the existing Q3 canonical
   approximation family.
2. **Moving probe** — reoptimizing `q_N` can manufacture an attractive `β_N` profile without
   producing one form inequality on a common core.
3. **Wrong numerator** — the prolate deficit's `e^{−4πλ²}` scale can be substituted for the
   actual residual numerator without a theorem.

The first and third are **C04/C10** failures. The second is **C09**. That is why the index,
normalization, fixed-probe, and source-object locks must precede interpretation.

## 10. Final proposal

```text
Phase 0:  CCM_D0_MODE_INDEX_CROSSWALK + dual normalization lock
          + independent matrix-entry checks.
Phase 1:  one no-fit control-cell penalty run at λ²=13, N=120.
Phase 2:  fixed-λ, fixed-q β_N profile across a precommitted N ladder.
Phase 3:  N-stabilized sectional-gap and actual-numerator rate profile
          across a precommitted λ² grid.
Only after green source lock and finite certificates:  CCM_SIEG_of_penalty.
```

The run is worth doing. `SIEG_of_penalty` is not the prerequisite.

### Meta closeout

**What became smaller?** "Try our theorem on their matrices" became one exact finite
instrument: source-locked basis + exact normalization split + fixed-`q` penalty profile +
rate-comparison profile.

**What was killed?** Waiting for `SIEG_of_penalty` before feasibility; 057.2 as the
transfer-deciding probe; binary `P-Δ`; the proposed ternary as exhaustive; `δ_N(ξ) = 1` as an
`L²`-normalization; `1 − χ₂` as the already-proved input-B numerator.

**Current smallest named gap:** `CCM_D0_MODE_INDEX_AND_NORMALIZATION_CROSSWALK`

**Next cheapest decisive test:** reconstruct the `(m,N) = (13,120)` basis, one diagonal and
one off-diagonal matrix entry, the reversal involution, and both normalization functionals
without fitting any scalar.

**Prediction fate:** `G = I` CONFIRMED · `κ` and `λ² = m` CONFIRMED · `J` commutes with `K`
CONFIRMED independently from the primary source · old binary `P-Δ` INVALID PREDICTION OBJECT,
no outcome score assigned · new `P-DELTA-R` REGISTERED, untested.

```yaml
iteration:
  target: CCM_penalty_instrument_and_gap_profile
  status: OPEN
  failed_strategy: interpret_sectional_gap_or_prolate_proxy_as_the_operator_input_B_ratio
  cognitive_operator_used: UNIT_AUDIT
  new_gap_name: CCM_D0_MODE_INDEX_AND_NORMALIZATION_CROSSWALK
  invariant_learned: one fixed source probe, one exact basis, and two distinct normalizations must survive every N and lambda comparison
  forbidden_future_move: reoptimize_q_per_N_or_use_delta_N_anchor_as_G_norm
  next_decisive_test: no_fit_control_cell_13_120_source_crosscheck
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS: RUN_CCM_PENALTY_CROSSWALK_BETA_DELTA_PROFILE
MODE: READ_ONLY_EXPERIMENTAL_AFTER_OPERATIONAL_RELEASE
REPO: Malaeu/chen_q3
BRANCH: rh_clean
EXPECTED_HEAD: fa038f59451da81c82f94da4234d22b66d6214fd
REPO_WRITE_AUTHORIZED: false
ARISTOTLE_SUBMISSION: NONE
NEW_CHAT: false
TRANSACTION: CCM_PENALTY_SOURCE_LOCK_AND_RATE_PROFILE
STOP: CCM_PENALTY_SOURCE_LOCK_OR_PROFILE_UNCLASSIFIED
SUCCESS: CCM_PENALTY_SOURCE_LOCK_AND_RATE_PROFILE_CLASSIFIED

READ_FIRST:
  - docs/routeB_bus/maps/RECON_2026-08-07_CCM_ORIGINAL.md
  - docs/routeB_bus/PACKET_2026-08-07_INSTRUMENT_AND_GAP.md
  - docs/routeB_bus/maps/ZOOM_2026-08-07_GAP_TRANSFER_THROUGH_GALERKIN.md
  - q3.lean.aristotle/Q3/Proofs/RouteB/H2aPenaltyCoercivity.lean
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0LogWindowMeasureTransport.lean
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0KTrialStage1.lean

PHASE_0_SOURCE_LOCK:
  required:
    - verify HEAD and all referenced file hashes
    - pin the exact version and source of any connes-cvs implementation
    - derive lambda^2=m and L=log m without fitting
    - identify paper N with PairIndex.N
    - identify mode order -N through N
    - verify V_CCM equals the project transported mode
    - verify G=I
    - construct J as mode reversal
    - verify J^2=I and JK=KJ
    - lock K=W_0,2-W_R-W_prime
    - verify prime cutoff k<=lambda^2
    - reconstruct at least one diagonal and one off-diagonal K entry independently
  on_failure:
    stop: CCM_PENALTY_SOURCE_CROSSWALK_MISMATCH
    run_numerics: false

K6_PRECOMMIT:
  control_cell: {m: 13, lambda: sqrt_13, N: 120}
  q_source:
    object: projected_source_prolate_trial
    may_depend_on_computed_ground_eigenvector: false
  q_normalization: {condition: q_star_q_equals_1}
  theorem510_normalization:
    condition: delta_N_xi_equals_1
    same_as_q_normalization: false
  matrix_orientation: {K: W_0_2_minus_W_R_minus_W_prime, G: identity, J: mode_reversal}
  no_fitted_scalar: true

PHASE_1_CONTROL_CELL:
  required:
    - build K G J and q at m=13 N=120
    - verify q is nonzero and J-even
    - normalize q in G norm
    - compute a=q_star_K_q
    - search beta>a and tau>=0
    - use arbitrary precision with precision doubling
    - distinguish approximate eigenvalue search from interval PSD certification
  outcomes:
    - CCM_CONTROL_CELL_CERT_INTERVAL_PASS
    - CCM_CONTROL_CELL_REGISTERED_CERT_FAIL
    - CCM_CONTROL_CELL_NUMERICALLY_INCONCLUSIVE
  semantic_rule: failure_of_one_penalty_certificate_does_not_negate_even_simple

PHASE_2_BETA_N:
  prerequisite: {phase_0_pass: true}
  precommit_before_values:
    - fixed lambda
    - finite N ladder
    - base N0
    - one fixed q in E_N0
    - zero-padding embedding into every larger E_N
    - precision levels
    - beta search tolerance
  required_outputs: [a, beta_N_star, beta_N_star_minus_a, tau_required, PSD lower envelope, retained precision]
  separate_diagnostic:
    moving_projected_q_N_allowed: true
    label: MOVING_PROBE_DIAGNOSTIC_NOT_TRANSFER_EVIDENCE

PHASE_3_DELTA_RATE:
  prerequisite: {phase_0_pass: true}
  requirements:
    - precommit lambda_squared grid before evaluating matrices
    - use an N ladder at every lambda
    - exclude lambda values without N stabilization
    - compute global sectional gap
    - compute even-sector and odd-sector competitors separately
    - record local slope of log Delta against lambda_squared
    - record cumulative effective rate
    - record actual trial-numerator rate when available
    - record prolate leakage proxy separately
    - record slope of log numerator_over_Delta
    - attach precision-floor and conditioning diagnostics

RATE_CLASSES:
  - DELTA_SUBEXPONENTIAL_IN_LAMBDA_SQUARED
  - DELTA_EXPONENTIAL_SUBCRITICAL_TO_NUMERATOR
  - DELTA_CRITICAL_SAME_EXPONENTIAL_RATE
  - DELTA_SUPERCRITICAL_FASTER_THAN_NUMERATOR
  - DELTA_RATE_UNRESOLVED

MANDATORY_PLANTS:
  - {id: P_R6_1_INDEX_LENGTH, mutation: lambda_equals_m_or_L_equals_log_lambda, expected: CCM_D0_INDEX_LENGTH_CROSSWALK_MISMATCH}
  - {id: P_R6_2_PRIME_SIGN, mutation: add_prime_matrix_instead_of_subtract, expected: CCM_WEIL_MATRIX_ORIENTATION_MISMATCH}
  - {id: P_R6_3_NORMALIZATION, mutation: use_delta_N_normalized_probe_without_G_unit_normalization, expected: CCM_PENALTY_PROBE_NOT_G_UNIT}
  - {id: P_R6_4_MOVING_PROBE, mutation: claim_transfer_from_independently_reoptimized_q_N, expected: CCM_BETA_N_MOVING_PROBE_NOT_TRANSFER_EVIDENCE}
  - {id: P_R6_5_PROXY, mutation: replace_actual_input_B_numerator_by_one_minus_chi_2, expected: CCM_PROLATE_PROXY_AS_INPUT_B_NUMERATOR}

VALIDATION:
  - exact source/provenance ledger
  - independent paper-formula matrix-entry checks
  - Hermitian residual
  - J involution and commutation residual
  - q G-norm residual
  - Rayleigh value reality
  - interval or directed-rounding PSD check where certification is claimed
  - precision doubling
  - conditioning report
  - no float64 route verdict
  - all plants fire
  - no repository mutation
  - exact environment and package-version report

REPORT_REQUIRED:
  - exact source pin
  - exact implementation pin
  - CCM_D0 index crosswalk
  - distinct q-unit and delta_N normalization sections
  - control-cell result
  - fixed-q beta_N profile
  - moving-q diagnostic kept separate
  - N-stabilized Delta rate table
  - actual numerator versus prolate proxy table
  - rate classification
  - plant fates
  - strongest unresolved ambiguity
  - no claim of SlotH2a closure
  - no claim of all-lambda input A
  - no route promotion
  - ROUTE CHALLENGER_NOT_RH
  - BUS_010 VOID
  - GOAL_055 HOLD
  - PX_RH_CLAIM NOT_MADE

NOT_AUTHORIZED:
  - implement CCM_SIEG_of_penalty
  - modify Q3.Main
  - edit Goal 055
  - create Bus 010
  - submit Aristotle
  - promote Route B
  - claim PX or RH
```

---

**Материализовано** телом Linux 2026-08-07 (владелец работает на этой машине; тело Mac
сегодня не активно, последний его коммит `7dbfb431` от 2026-08-06 23:16).
Пин вердикта `fa038f59` — предок текущего HEAD, проверено `merge-base --is-ancestor`.
Источники цитирования в оригинале: arXiv 2511.22755, 2602.04022, 2605.20224.
