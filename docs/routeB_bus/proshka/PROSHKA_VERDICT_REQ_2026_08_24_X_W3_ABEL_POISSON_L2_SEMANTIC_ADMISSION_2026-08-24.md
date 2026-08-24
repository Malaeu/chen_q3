# STATUS: PROVED — W3 SELECTED FERRERS ABEL–POISSON L2 LOCK IS SEMANTICALLY ADMITTED

```yaml
PRIMARY: SEMANTICALLY_ADMIT_W3_SELECTED_FERRERS_ABEL_POISSON_L2_LOCK
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-24-X
DOCUMENT_ROLE: INDEPENDENT_POST_KERNEL_SEMANTIC_VERDICT

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  TRANSACTION_COMMIT: 01ee6f43822c3a7515dc56c76e0334de2a7e6b14
  TRANSACTION_PARENT: 636e075d915449b382096a00843a7e91f5273dce
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersAbelPoissonL2.lean
  LEAN_BLOB: a064544af242608b8d09b94931412d1bccd5c392
  LEAN_SHA256: fcadf926f2bc57a019f9f61aade993e08f2af0c071bc7cde11ab3b3d4b0dd93f
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_3C_1_12_SELECTED_FERRERS_ABEL_POISSON_L2_2026-08-23.md
  SOURCE_RECORD_BLOB: b5eae9fbd69f8e22d78c66d53ada3a5839c0ec4c
  RECEIPT: PASS

KERNEL_GATE_REPORTED:
  AUTHOR_OF_LEAN_SOURCE: CODEX
  GATES_RUN_BY: LINUX_CLAUDE
  lake_env_lean: EXIT_0_ZERO_ERRORS_ZERO_WARNINGS_7_AXIOM_PRINTS
  target_build: PASS_7850_JOBS
  q3_check: EXIT_0
  q3_main_build: PASS_7809_JOBS
  strict_spine: PASS
  semantic_index: PASS
  sorry_admit_native_decide: ABSENT
  AXIOM_PROFILE_ALL_7:
    - propext
    - Classical.choice
    - Quot.sound
  JUDGE_RERAN_KERNEL: false

SEMANTIC_ADMISSION:
  W3_SELECTED_FERRERS_ABEL_REFLECTED_L2_LOCK: PROVED
  exact_packet: selectedFerrersLemma73SourcePacket_k
  exact_packet_scale: selectedFerrersLemma73SourceScale_k
  endpoint_convention: PRODUCTION_FULL_ENDPOINT
  packet_real_valuedness_required: false
  packet_evenness_used: true
  packet_zero_mass_used: true
  reflected_abel_object: EXACT_POSITIVE_FREQUENCY_ABEL_SUM
  reflected_abel_scale: U_POW_MINUS_ONE_HALF
  fourier_convention: PROJECT_REAL_FOURIER_WITH_2PI
  target_object: E_STAR_PACKET_PLUS_HALF_CENTER_SHADOW
  target_shadow_sign: PLUS
  target_shadow: ONE_HALF_PACKET_ZERO_TIMES_SQRT_U
  convergence_parameter: R_TENDS_TO_ONE_WITHIN_Ioo_0_1
  measure: DSTAR_RESTRICT_EXACT_SELECTED_IM_WINDOW
  convergence_category: SQUARED_L2_INTEGRAL_TENDS_TO_ZERO
  seam_equality_category: ALMOST_EVERYWHERE_ONLY
  pointwise_full_endpoint_midpoint_identification: FORBIDDEN_AND_ABSENT
  dirichlet_jordan_used: false
  fitted_constant_used: false
  numerical_input_used: false

PUBLIC_SURFACE:
  selectedFerrersReflectedAbel:
    status: ADMITTED_DEFINITION
  selectedFerrersAbelLimit:
    status: ADMITTED_DEFINITION
  selectedFerrersReflectedAbel_memLp:
    status: ADMITTED_THEOREM
  selectedFerrersAbelLimit_memLp:
    status: ADMITTED_THEOREM
  selectedFerrersReflectedAbel_tendsto_L2:
    status: ADMITTED_THEOREM

PLANTS:
  FULL_ENDPOINT_VS_MIDPOINT_ESTAR_SEAM: PASS
  ZERO_MASS_IS_LOAD_BEARING: PASS
  POINTWISE_WITHOUT_DOMINATION_DOES_NOT_GIVE_L2: PASS
  COMPLEX_EVEN_DOES_NOT_REQUIRE_REAL_VALUEDNESS: PASS

SCOPE_FIREWALL:
  universal_in_k: true
  fixed_k_abel_limit: true
  uniform_in_k_rate: false
  shifted_root_energy: NOT_PROVED
  shifted_form_domain_membership: NOT_PROVED
  cofinal_root_energy_rate: NOT_PROVED
  route_promotion: false
  rh_claim: false

CLOSES:
  - W3_SELECTED_FERRERS_ABEL_REFLECTED_L2_LOCK
OPENS: []

PROCESS_FINDING_NONBLOCKING:
  CODE: PUSHED_CLOSEOUT_MUTATED_IN_PLACE
  PATH: q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_DLMF_FULL_FINITE_SPECTRUM_CROSSWALK_CLOSEOUT_2026-08-14.md
  OLD: AUTOPSY_dropped_SPECTRAL_LIMIT
  NEW: AUTOPSY_dropped_SPECTRAL_ORDERING
  VIOLATED_RULE: SUPPLIER_CONTRACT_APPEND_ONLY_AFTER_PUSH
  BLOCKS_W3_SEMANTIC_ADMISSION: false
  ACTION:
    - do_not_mutate_that_closeout_again
    - future_closed_enum_repairs_use_a_new_append_only_migration_or_addendum
    - this_verdict_does_not_ratify_the_semantic_choice_of_the_replacement_tag

NEXT_LOAD_BEARING_GAP: W4_FIXED_K_SHIFTED_ROOT_ENERGY

NEXT_TRANSACTION:
  TASK_ID: H2A_4_1B_3C_1_13_W4_FIXED_K_SHIFTED_ROOT_ENERGY_SOURCE_AND_API_PREFLIGHT
  MODE: READ_ONLY_MATH_AND_API_PREFLIGHT
  EXECUTION_AUTHORIZED_UNDER_STANDING_NIGHT_GRANT: true
  LEAN_EDIT: false
  NUMERICS: false
  ARISTOTLE: false
  OUTPUT_PATH: docs/routeB_bus/H2A_4_1B_3C_1_13_W4_FIXED_K_SHIFTED_ROOT_ENERGY_PREFLIGHT_2026-08-24.md

SELECTED_REPRESENTATION:
  CODE: LOG_COORDINATE_FINITE_JUMP_FOURIER_DECAY
  KILL_POWER: 9
  COST: 5

RUNNER_UP_NOT_AUTHORIZED_FOR_LEAN:
  CODE: DIRECT_PIECEWISE_AC_WEIGHTED_ROOT_ENERGY
  KILL_POWER: 8
  COST: 6

ARSENAL_MANDATE:
  ACCEPTED: true
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C10_FUNCTIONAL_NOT_SURROGATE
    - C13_RESTORE_SYMMETRY_BY_EXPLICIT_SHADOW

PRIOR_PREDICTION_FATES:
  P_W3_LEAN_1_0_78: CONFIRMED
  P_W3_LEAN_2_0_70: CONFIRMED
  P_W3_LEAN_3_0_86: CONFIRMED
  LIKELIEST_FAILURE_POISSON_APPROXIMATE_IDENTITY_MEASURABILITY_OR_NORMAL_FORM_API: REFUTED_AS_BLOCKER
  RETROACTIVE_REPAIR: false

REGISTERED_PREDICTIONS:
  P_W4_1:
    probability: 0.82
    prediction: the exact additive-log representative of the W3 limit is piecewise absolutely continuous with finitely many jumps for each fixed k
  P_W4_2:
    probability: 0.78
    prediction: one integration-by-parts decay bound plus the exact logarithmic arch-symbol domination proves fixed-k shifted root energy
  P_W4_3:
    probability: 0.99
    prediction: W4 supplies no uniform or cofinal root-energy rate
  LIKELIEST_FAILURE: LOG_COORDINATE_DERIVATIVE_OR_SEAM_JUMP_LEDGER_SOURCE_GAP

SCOPE: ABSTRACT
VERIFIER: LEAN
PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

| Node | Verdict | Exact boundary | Tags |
|---|---|---|---|
| **W1 actual-Fourier crosswalk** | **PROVED** | The synthesized source log-window Fourier image equals almost everywhere the ordinary Fourier integral of the exact additive zero extension. | `[ABSTRACT][LEAN]` |
| **W2 selected packet variation** | **PROVED** | The exact source-scaled production packet, retaining full endpoint values, has bounded variation on `Set.univ`. | `[ABSTRACT][LEAN]` |
| **W3 Abel–Poisson `L²` lock** | **PROVED AND SEMANTICALLY ADMITTED** | For every selected `k`, the exact reflected Abel family converges in squared `L²(dStar|I_m)` to `E_star(f_k) + 1/2 f_k(0) sqrt(u)`. | `[ABSTRACT][LEAN]` |
| **W4 fixed-`k` shifted root energy** | **OPEN** | Must prove that the exact W3 limit, transported through the source log-window Fourier crosswalk, belongs to the shifted Archimedean form domain for each fixed `k`. | `[ABSTRACT][CONDITIONAL]` |
| **W5 cofinal rate** | **OPEN LATER** | No uniform growth rate in `k` follows from W1–W4. | `[COFINAL_FAMILY][CONDITIONAL]` |

## 1. Exact task and exact source object

The public reflected family is definitionally

\[
A_{k,r}(u)
=
(\sqrt u)^{-1}
\sum_{n\ge1}r^n\,\mathcal F(f_k)(n/u),
\qquad 0\le r<1,
\]

where

```text
f_k = selectedFerrersLemma73SourcePacket k.
```

This is the exact complex source-scaled selected Ferrers production packet. The file does not replace it by an adjacent mode, a midpoint packet, a real-valued packet, or an abstract bounded-variation witness. `[ABSTRACT][LEAN]` **[C04][C10]**

The target is definitionally

\[
A_{k,1}^{\mathrm{target}}(u)
=
E_\star(f_k)(u)
+
\frac12 f_k(0)\sqrt u.
\]

The sign is the source-locked plus sign. The extra term is the explicit C13 shadow left after the zero-mass packet removes the Fourier zero-frequency term. `[ABSTRACT][LEAN]` **[C13]**

## 2. The Fourier and Poisson normalization is exact

The source proves, rather than assumes, that the finite periodization has Fourier coefficient

\[
\widehat p_{k,u}(n)
=
u^{-1}\mathcal F(f_k)(n/u).
\]

Its local circle kernel is

\[
P_r(x)=
\frac{1-r^2}
{1-2r\cos(2\pi x)+r^2},
\]

with nonnegativity, exact unit mass, and its positive/negative geometric Fourier expansion established in the pinned API. Exact complex evenness gives

\[
\widehat f_k(-\xi)=\widehat f_k(\xi),
\]

without any real-valuedness premise. Exact zero mass removes the constant Fourier coefficient. Consequently the file proves the literal identity

\[
A_{k,r}(u)
=
\frac{\sqrt u}{2}(P_r*p_{k,u})(0)
\]

on the selected multiplicative window. There is no empirically inserted `2π`, factor two, phase, or sign. `[ABSTRACT][LEAN]`

## 3. The full-endpoint/midpoint boundary is preserved

The source does not claim pointwise agreement at a support seam. It defines a finite seam set containing every selected scale at which an active translate can hit either production endpoint. Outside this set, the finite periodization is continuous at both `0` and `1`, and periodic reindexing identifies the two endpoint values.

The production center identity is exact:

\[
\frac{\sqrt u}{2}
\sum_{z\in\mathbb Z}f_k(uz)
=
E_\star(f_k)(u)+\frac12f_k(0)\sqrt u.
\]

At seam scales the midpoint and full-endpoint values may differ. The source uses only that the finite seam set is null for `dStar`; it never promotes almost-everywhere equality to pointwise equality. The mandatory seam plant distinguishes the two categories. `[ABSTRACT][LEAN]` **[C04]**

## 4. The approximate-identity step is source-legal

The pinned continuous-source periodization theorem is not used. Instead, compact support gives a finite source-specific periodization.

The Poisson kernel is split across `[0,1/2]` and `[1/2,1]`. Each half has exact mass `1/2`. A pinned peak-integral theorem is applied separately at `0` and `1`, and exact periodicity reassembles the center value. This proves off-seam pointwise convergence without importing Dirichlet–Jordan or applying a theorem whose source class excludes endpoint jumps. `[ABSTRACT][LEAN]` **[C10]**

## 5. The `L²` conclusion has a genuine dominator

Both the Abel family and its exact target are strongly measurable on the selected window. The packet has a fixed global norm bound. Finite periodization preserves a fixed bound for each selected `k`; positivity and unit mass of the Poisson kernel transfer that bound uniformly in `r`.

Thus the squared difference is dominated by one integrable constant on the finite measure space

\[
\left(I_m(\mathrm{selectedFerrersPreAnchorIndex}(k)),d^\star u\right).
\]

Off-seam pointwise convergence and nullity of the seam set then feed filter-form dominated convergence. The public theorem concludes exactly

\[
\int_{I_m}
|A_{k,r}(u)-A_{k,1}^{\mathrm{target}}(u)|^2\,d^\star u
\longrightarrow0.
\]

The plant using moving unit vectors under counting measure correctly rejects the forbidden shortcut from pointwise convergence alone. `[ABSTRACT][LEAN]`

## 6. Scope firewall

W3 is universal in the selected natural-number index `k`, but the limit is taken in `r` for each fixed `k`. Therefore W3 proves a family of fixed-cell `L²` convergence theorems; it does not provide a uniform rate in `k`.

W3 does **not** prove:

```text
shifted Archimedean form-domain membership;
logarithmically weighted root energy;
a quantitative root-energy bound;
a cofinal root-energy rate;
ground-state tracking;
route promotion;
RH.
```

Calling W3 a fixed-`k` shifted-root-energy theorem would be a C10 functional substitution. `[ABSTRACT][LEAN]` **[C10]**

## 7. Kernel receipts and independent semantic review

I did not rerun Lean. The transaction reports that Codex wrote the source and a separate Linux body ran direct Lean, the target build and `q3_check`; it reports the standard axiom triple for all three public theorems and all four plants, with no `sorry`, `admit` or `native_decide`.

This verdict independently audited the exact committed source object, Fourier scale, endpoint category, measure, quantifiers and conclusion. On that basis the declarations are released from semantic quarantine and may now be consumed by downstream Route-B nodes within the scope above. `[ABSTRACT][LEAN]`

## 8. Nonblocking process finding

The W3 commit also changed one line in an already pushed historical closeout:

```text
AUTOPSY: dropped=SPECTRAL_LIMIT
```

became

```text
AUTOPSY: dropped=SPECTRAL_ORDERING.
```

This violates the repository's append-only rule for pushed artifacts. The fix should have been a new migration/addendum artifact. It does not alter any W3 definition, theorem, import, premise or proof term, so it does not block W3 semantic admission.

This verdict does not judge whether `SPECTRAL_ORDERING` is the best semantic replacement for the unavailable enum token. Do not mutate the historical closeout again; preserve this incident as a process autopsy. `[ABSTRACT][PAPER]`

## FINAL PROPOSAL

Freeze W3 as proved. Do not reopen its packet, scale, seam convention or Poisson representation.

The next load-bearing node is not a cofinal estimate. It is the fixed-`k` theorem

```text
W4_FIXED_K_SHIFTED_ROOT_ENERGY.
```

Before writing Lean, run one read-only object/API preflight. It must identify the exact additive-log representative of `selectedFerrersAbelLimit`, enumerate every finite jump and derivative piece, and state the exact weighted `L²` conclusion consumed by the shifted Archimedean form-domain receiver.

The primary representation is finite-jump Fourier decay in additive log coordinates. The runner-up is a direct piecewise-absolutely-continuous weighted-energy proof. Neither is authorized for Lean until the preflight chooses one exact theorem packet.

## STRONGEST ATTACK

The strongest objection is:

> The kernel-green source may prove convergence for a smooth or midpoint surrogate, while the downstream consumer needs the discontinuous production packet with full endpoint values.

The objection fails. The source packet is exactly `selectedFerrersLemma73SourcePacket`; the target center identity retains full endpoint values; the only category weakening is explicit removal of the finite seam set in an almost-everywhere argument. The seam plant proves why pointwise replacement is illegal. **[C04][C10]**

The strongest surviving objection is different:

> `L²` convergence to the W3 limit does not imply membership in the shifted form domain.

This objection is correct and is exactly W4. A logarithmic weight can make a function lie in ordinary `L²` while its shifted root energy diverges. W3 therefore closes no part of W4 by lower semicontinuity or wishful passage to the limit.

## CODEX DIRECTIVE

```text
TASK_ID:
  H2A_4_1B_3C_1_13_W4_FIXED_K_SHIFTED_ROOT_ENERGY_SOURCE_AND_API_PREFLIGHT

MODE:
  READ_ONLY_MATH_AND_API_PREFLIGHT

AUTHORITY:
  standing night grant

SOURCE_LOCK:
  W1:
    q3.lean.aristotle/Q3/Proofs/RouteB/
    D0PstarSourceLogWindowFourierIntegralCrosswalk.lean
  W2:
    q3.lean.aristotle/Q3/Proofs/RouteB/
    G6N1SelectedFerrersPacketVariation.lean
  W3:
    q3.lean.aristotle/Q3/Proofs/RouteB/
    G6N1SelectedFerrersAbelPoissonL2.lean
  SYMBOL:
    q3.lean.aristotle/Q3/Proofs/RouteB/
    D0PstarExactArchSymbolWeightedModeL2.lean
  DOMAIN_RECEIVERS:
    q3.lean.aristotle/Q3/Proofs/RouteB/
    D0PstarShiftedArchModeDomain.lean
    q3.lean.aristotle/Q3/Proofs/RouteB/
    D0PstarShiftedArchSesquilinearForm.lean

OBJECTIVE:
  Produce exactly one theorem-sized W4 packet proving fixed-k shifted root
  energy for the exact W3 target.  Do not write Lean.

MANDATORY AUDIT:
  1. Copy the exact downstream consumer type.
  2. Identify the exact additive-log function whose ordinary Fourier transform
     is the synthesized source image.
  3. Enumerate all discontinuities:
       selected-window endpoints;
       every finite E_star seam;
       any shadow-term junction.
  4. Prove on paper that the function is piecewise absolutely continuous, or
     name the smallest missing derivative-integrability lemma.
  5. Derive an explicit fixed-k bound
       |Fourier(g_k)(t)| <= C_k / (1 + |t|)
     or an exact stronger substitute.
  6. Match the bound to the exact project arch-symbol weight and shifted-form
     receiver.  Do not replace the exact symbol by an unnamed logarithmic
     surrogate.
  7. Keep fixed-k finiteness separate from every cofinal rate.

CANDIDATE_A:
  LOG_COORDINATE_FINITE_JUMP_FOURIER_DECAY
  kill_power: 9/10
  cost: 5/10

CANDIDATE_B:
  DIRECT_PIECEWISE_AC_WEIGHTED_ROOT_ENERGY
  kill_power: 8/10
  cost: 6/10

MANDATORY_PLANTS:
  - L2_WITHOUT_LOG_WEIGHTED_ENERGY
  - FULL_ENDPOINT_VS_MIDPOINT_SEAM
  - ORDINARY_FOURIER_VS_SYNTHESIZED_ISOMETRY
  - FIXED_K_FINITE_NOT_COFINAL_RATE

SUCCESS:
  W4_FIXED_K_SHIFTED_ROOT_ENERGY_THEOREM_PACKET_LOCKED

FAILURES:
  W4_LOG_COORDINATE_SOURCE_OBJECT_MISMATCH
  W4_FINITE_JUMP_DECAY_API_GAP
  W4_SHIFTED_SYMBOL_WEIGHT_CROSSWALK_GAP
  W4_FIXED_K_ROOT_ENERGY_PREFLIGHT_INCONCLUSIVE

FORBIDDEN:
  no Lean edits;
  no Aristotle;
  no numerics;
  no pointwise midpoint/full-endpoint identification;
  no L2-to-form-domain shortcut;
  no cofinal rate claim;
  no Route/RH promotion.

OUTPUT EXACTLY:
  docs/routeB_bus/
  H2A_4_1B_3C_1_13_W4_FIXED_K_SHIFTED_ROOT_ENERGY_PREFLIGHT_2026-08-24.md
```

## META CLOSEOUT

**What became smaller?**

```text
W3 kernel-green but quarantined
→ exact W3 theorem semantically admitted.
```

**What was killed?**

```text
real-valuedness as a hidden premise;
continuous-source periodization for the jumping packet;
midpoint/full-endpoint pointwise substitution;
pointwise convergence without domination;
Dirichlet–Jordan as a required W3 supplier.
```

**What must not be tried again?**

```text
using W3 as shifted root energy;
using W3 as a cofinal rate;
reopening the exact plus shadow sign;
mutating a pushed closeout to repair an enum token.
```

**Current smallest named gap:**

```text
W4_FIXED_K_SHIFTED_ROOT_ENERGY.
```

**Next cheapest decisive test:**

```text
Lock the exact additive-log finite-jump representation and determine whether
one integration-by-parts estimate supplies the exact weighted root-energy
consumer.
```

**Prior prediction fate:** all three registered W3 Lean predictions were confirmed without retroactive repair; the predicted Poisson API failure did not occur.

```yaml
iteration: H2A_4_1B_3C_1_12
target: W3_SELECTED_FERRERS_ABEL_REFLECTED_L2_LOCK
status: PROGRESS
failed_strategy: DIRECT_BV_DIRICHLET_JORDAN_AS_PRIMARY_W3_ROUTE
cognitive_operator_used: MINIMAL_LEMMA
new_gap_name: W4_FIXED_K_SHIFTED_ROOT_ENERGY
invariant_learned: full endpoint values remain literal and seams are weakened only almost everywhere under the exact dStar measure
forbidden_future_move: do not infer shifted form-domain membership from ordinary L2 convergence
next_decisive_test: W4 fixed-k log-coordinate finite-jump source/API preflight
progress_class: PROOF_PROGRESS
route_score: 5
```
