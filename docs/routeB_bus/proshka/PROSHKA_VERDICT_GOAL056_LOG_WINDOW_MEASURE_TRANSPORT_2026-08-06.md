# STATUS: OPEN — LOG-WINDOW MEASURE TRANSPORT SELECTED; ORTHONORMALITY IS ITS SOLE FIRST CONSUMER

```yaml
PRIMARY: G6_S2_D0_LOG_WINDOW_MEASURE_TRANSPORT_SELECTED
PRIMARY_COUNT: 1

OPERATIVE_CLASS: TRY_D0_LOG_WINDOW_MEASURE_TRANSPORT_AND_ORTHONORMALITY
OPERATIVE_CLASS_COUNT: 1
SELECTED_PATH: B

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  PIN: 1553624ae27944b93ef3adce265dc8e8e5c21b33
  ORIGIN_HEAD_EQUALS_PIN: true
  PIN_COMMIT: "[MacOS][rh_clean][RouteB] Materialize Goal 056 residual contract"

CONTROL:
  CODEX_CONTROL_STATUS: ACTIVE
  CODEX_CONTROL_SHA256: fc77ff8d7483c87744f07e8aea3d59b08f9b5340541d3bf414885f239dfafc4e
  AUTHORITY: CODEX_PLUS_PROSHKA
  OWNER_DEFERRAL_ALLOWED: false
  SOLE_OWNER_GATE: PX_RH_CLAIM

ARSENAL:
  MANDATE_ACCEPTED: true
  DECK_SHA256: 018dbf6b5be6f21b2346ac29bf910d7c898d0352b72f9b67cfddf6865243839d
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

PHASE_4A:
  FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzCenteredCoordinateLock.lean
  SHA256: ce0226f7bd028449a04cae0dfa28e8998a0e835eba5ec0a56a93f0ae18b073a5
  SOURCE_FAMILY_LOCK: PROVED
  PARENT_EXTRACT_LOCK: PROVED
  RAW_ARGUMENT: -z
  GWIN_ARGUMENT: -I*z
  DEFECT_ORIENTATION: RAW_MINUS_SCALED_GWIN
  DEFECT_ZERO_OR_DECAY: NOT_PROVED

PHASE_4B:
  FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzGalerkinResidualContract.lean
  SHA256: 1f9b0f16210271fc699107f991a244421d98bbdafd695d5a585dae4aca4f73ff
  CLOSEOUT_SHA256: 2bf9914411783bb1122e38143193576ff7d369b94d2bacd21d36c0133d58b659
  RESULT: G6_S2_NAMED_OBJECT_RESIDUAL_CONDITIONAL_RECEIVER_MATERIALIZED
  CONTRACT_STATUS: EXPLICIT_LOCAL_HYPOTHESIS_NOT_AXIOM_NOT_PROVED
  OBJECT_RESIDUAL: NORMALIZED_PROJECTION_MINUS_FULL
  COMPACT_OPEN_DECAY: SEPARATE_OPEN_WALL

SELECTED_TRANSACTION:
  NAME: G6_S2_D0_LOG_WINDOW_MEASURE_TRANSPORT_AND_ORTHONORMALITY
  OWNED_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0LogWindowMeasureTransport.lean
  SOLE_IMPORT: Q3.Proofs.RouteB.D0KTrialStage1
  NAMESPACE: Q3.RouteB.D0Pstar
  PUBLIC_DEFINITIONS: 0
  PUBLIC_THEOREMS: 2
  PRIVATE_HELPERS_ALLOWED: true
  PROGRESS_CLASS: PROOF_PROGRESS
  COGNITIVE_OPERATOR: MINIMAL_LEMMA

PUBLIC_THEOREMS:
  - integral_comp_logWindow_dStar
  - V_n_m_orthonormal

DIRECT_DOWNSTREAM_CONSUMER:
  Q3.RouteB.D0Pstar.coe_P_m_N_apply_eq_sum_inner_V_n_m_smul

DIRECT_CONSUMER_AUTHORIZED: false

STOP: G6_S2_D0_LOG_WINDOW_MEASURE_TRANSPORT_MISSING
SUCCESS: G6_S2_D0_LOG_WINDOW_TRANSPORT_AND_V_MODES_ORTHONORMAL_PROVED

PHASE_KEY_CHANGE: false
NEW_CHAT: false

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ARISTOTLE_SUBMISSION: NONE
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

## 1. Pin and production-surface audit

`origin/rh_clean` resolves exactly to `1553624ae27944b93ef3adce265dc8e8e5c21b33`. The commit is the Phase-4B materialization commit stated in the request.  `[ABSTRACT][PAPER]`

The active Spine records the exact supplied `CODEX_CONTROL.md` SHA-256, active executor status, `CHALLENGER_NOT_RH`, Bus 010 `VOID`, and PX/RH as the sole owner boundary.  `[ABSTRACT][PAPER]`

The Arsenal deck is reachable and its materialization ledger records the required byte SHA-256 `018dbf6b…3839d`. The standing attack-duals are accepted.    `[ABSTRACT][PAPER]`

### Phase 4A

The production module still uses one literal selected index

```lean
S.canonical.parent (S.canonical.extract k)
```

and defines:

```text
selectedRawTransformCoordinate S k z
  = rawFplus ... (-z)

selectedGwinTransformCoordinate S k z
  = Gwin h λ (-I*z)

selectedGalerkinCoordinateDefect
  = selectedRawTransformCoordinate
    - selectedScaledGwinTransformCoordinate.
```

It proves the exact selected-family decomposition while explicitly withholding defect-zero, defect convergence, and `SlotS2`.  `[COFINAL_FAMILY][LEAN]`

### Phase 4B

Phase 4B defines the literal object residual as

```lean
(selectedTrialNormalizer S k : ℂ) •
  ((gTrial_m_N i h hLp : H_m i) - gTrial_m i h hLp)
```

on that same selected index, and defines its coordinate against

```text
dStar.restrict (I_m i)
```

with kernel

```text
(u : ℂ) ^ (-I*z).
```

The crosswalk remains a `Prop` hypothesis. No axiom or unconditional theorem supplies it.  `[COFINAL_FAMILY][LEAN]`

The closeout confirms the supplied production and answer SHA-256 values, direct Lean, target build 7775, full build 7817, `q3_check`, all four plants, standard-triple axioms, 67/67 orchestration tests, three SQLite integrity checks, and strict Spine. It also states that weighted Fourier orthonormality and projection reconstruction remain open.  `[COFINAL_FAMILY][LEAN]`

## 2. Decision among A–D

| Candidate                                                      | Verdict                 | Reason                                                                                                                                                                              |
| -------------------------------------------------------------- | ----------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **A — start directly with orthonormality**                     | Viable but not selected | It would either duplicate the weighted logarithmic change of variables privately or leave the same measure bridge to be reproved for the later Mellin coordinate.                   |
| **B — first materialize logarithmic-window measure transport** | **Selected**            | The source itself names the unitary coordinate map (x=\log(\lambda_m u)). The same transport controls both Fourier orthonormality and the later (du/u)-to-`Gwin` coordinate bridge. |
| **C — kill the route**                                         | Rejected                | There is no contradiction. The source normalization is exactly the standard normalized Fourier basis after the logarithmic substitution.                                            |
| **D — run a smaller discriminator**                            | Rejected                | API existence and type compatibility are already established. Any belief-changing test would have to prove the substantive change-of-variables identity itself.                     |

The selected operative class is therefore:

```text
TRY_D0_LOG_WINDOW_MEASURE_TRANSPORT_AND_ORTHONORMALITY
```

## 3. Why B is the smallest honest object

The source-locked D0.1 contract explicitly gives:

[
H_m=L^2([\lambda_m^{-1},\lambda_m],du/u),
]

[
x=\log(\lambda_m u),
]

[
\kappa_m f(u)=f(\log(\lambda_m u)),
]

and declares (\kappa_m) unitary from (L^2([0,L_m],dx)) to (H_m). It then defines the normalized Fourier modes

[
U_{n,m}(x)=L_m^{-1/2}e^{2\pi i n x/L_m},
\qquad
V_{n,m}=\kappa_m U_{n,m}.
]

The same source fixes the inner product as antilinear in the first variable.  `[ABSTRACT][PAPER]`

The current Lean layer already defines the exact same objects:

```text
lambda_m i = sqrt i.m
L_m i      = log i.m
dStar       = volume.withDensity (ofReal u⁻¹)
I_m i       = Icc (lambda_m i)⁻¹ (lambda_m i)
H_m i       = Lp ℂ 2 (dStar.restrict (I_m i))
```

and

```lean
V_n_m i n u =
  (sqrt (L_m i))⁻¹ *
    exp (2*pi*I*n*(log (lambda_m i*u) / L_m i)).
```

`[ABSTRACT][LEAN]`

The missing fact is therefore not an invented convenience lemma. It is the unformalized source coordinate map already assumed by the mathematical dictionary.

Under **C04**, the `du/u` carrier and the Lebesgue logarithmic carrier are equal only after the Jacobian and endpoint map are proved. Under **C10**, orthonormality of a familiar-looking Fourier expression cannot substitute for orthonormality of the actual `Lp` objects. Under **C09**, the exact map and all conventions must be fixed before reconstruction cases are considered.

## 4. Exact production theorem statements

Owned file:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0LogWindowMeasureTransport.lean
```

Sole import:

```lean
import Q3.Proofs.RouteB.D0KTrialStage1
```

Namespace:

```lean
namespace Q3.RouteB.D0Pstar
```

The foundational file should not import Phase 4A or Phase 4B. Measure transport and Fourier orthonormality sit below those contracts; reversing that dependency would make a foundational source theorem depend on a later conditional receiver.

### 4.1 Public theorem 1 — exact measure transport

```lean
/--
The source logarithmic coordinate `x = log (lambda_m i * u)` transports
`dStar` on the exact multiplicative window `I_m i` to Lebesgue measure
on `Icc 0 (L_m i)`.

No continuity or integrability hypothesis on `F` is required; both sides use
the standard Bochner-integral convention when the integrand is not integrable.
-/
theorem integral_comp_logWindow_dStar
    (i : PairIndex) (F : ℝ → ℂ) :
    (∫ u : ℝ,
        F (Real.log (lambda_m i * u))
      ∂(dStar.restrict (I_m i))) =
      ∫ x : ℝ in Set.Icc 0 (L_m i), F x := by
  ...
```

`[ABSTRACT][CONDITIONAL]`

This is stronger and cleaner than a continuity-only interval-integral lemma. Pinned Mathlib v4.26 contains the general monotone one-dimensional change-of-variables theorem

```lean
MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn
```

which permits arbitrary Bochner integrands.  `[ABSTRACT][LEAN]`

The density conversion is also already available at the pinned Mathlib commit through:

```lean
MeasureTheory.restrict_withDensity
MeasureTheory.integral_withDensity_eq_integral_toReal_smul
```

`[ABSTRACT][LEAN]`

### 4.2 Public theorem 2 — the full integer Fourier family is orthonormal

```lean
/--
The exact source modes `V_n_m i n` form an orthonormal family in
`H_m i = L²(I_m i, du/u)`.
-/
theorem V_n_m_orthonormal (i : PairIndex) :
    Orthonormal ℂ (V_n_m i) := by
  ...
```

`[ABSTRACT][CONDITIONAL]`

The full (\mathbb Z)-indexed statement is preferable to a mode-set subtype theorem:

* it is the literal source theorem;
* it has the same proof cost;
* any finite `modeSet i` restriction follows by `Orthonormal.comp`;
* it is the correct input to later projection reconstruction.

Pinned Mathlib provides the exact target characterization:

```lean
orthonormal_iff_ite
```

[
\operatorname{Orthonormal}(v)
\iff
\langle v_i,v_j\rangle
======================

\begin{cases}
1,&i=j,\
0,&i\ne j.
\end{cases}
]

`[ABSTRACT][LEAN]`

It also defines the `Lp ℂ 2 μ` inner product as the integral of pointwise inner products:

```lean
MeasureTheory.L2.inner_def
```

`[ABSTRACT][LEAN]`

## 5. Proof route

### Step 1 — source arithmetic

Prove privately:

```lean
0 < lambda_m i
1 < lambda_m i
0 < L_m i
(lambda_m i) ^ 2 = i.m
Real.log ((lambda_m i) ^ 2) = L_m i
```

The existing lower bound `i.hm : 2 ≤ i.m` makes these elementary.

### Step 2 — exact image of the logarithmic coordinate

Let

```lean
φᵢ u := Real.log (lambda_m i * u).
```

Prove:

```lean
φᵢ '' I_m i = Set.Icc 0 (L_m i)
```

with the exact endpoint calculations:

[
\phi_i(\lambda_i^{-1})=0,
\qquad
\phi_i(\lambda_i)=L_i.
]

The inverse witness is:

[
u=\frac{e^x}{\lambda_i}.
]

This step fixes the interval rather than recovering it after the Fourier calculation.

### Step 3 — Jacobian and density

On `I_m i`:

[
\phi_i'(u)=u^{-1}.
]

Rewrite:

```text
dStar.restrict (I_m i)
```

as the restricted Lebesgue measure with density `ofReal u⁻¹`, convert the Bochner integral to the real scalar-weighted integral, and use positivity of every (u\in I_m) to simplify:

[
\operatorname{toReal}(\operatorname{ofReal}(u^{-1}))=u^{-1}.
]

Apply:

```lean
integral_image_eq_integral_deriv_smul_of_monotoneOn
```

to obtain `integral_comp_logWindow_dStar`.

This route uses the pinned general change-of-variables API, not a custom measure-theory reimplementation. The project is pinned to Mathlib v4.26.0 at commit `2df2f015…`.  `[ABSTRACT][LEAN]`

### Step 4 — pointwise inner-product orientation

For logarithmic coordinate (x), simplify the scalar inner product to:

[
\left\langle
L^{-1/2}e^{2\pi i n x/L},
L^{-1/2}e^{2\pi i r x/L}
\right\rangle
=============

L^{-1}e^{2\pi i(r-n)x/L}.
]

The difference is (r-n), not (n-r), because the first argument is conjugated.

### Step 5 — consume the transport theorem

Rewrite the `Lp` inner product with `L2.inner_def`, replace the `MemLp.toLp` representatives almost everywhere, and apply `integral_comp_logWindow_dStar`.

The remaining integral is the standard finite Fourier integral on ([0,L]).

The project already uses the relevant pinned APIs:

```lean
integral_exp_mul_complex
Complex.exp_int_mul_two_pi_mul_I
```

to prove the corresponding finite logarithmic Fourier mode cancellation.  `[ABSTRACT][LEAN]`

Split:

```text
n = r:
  integral = L;
  (sqrt L)⁻² * L = 1.

n ≠ r:
  r - n ≠ 0;
  endpoint exponential is exp(2*pi*I*(r-n)) = 1;
  integral = 0.
```

Then close `V_n_m_orthonormal` through `orthonormal_iff_ite`.

## 6. Source-convention ledger

| Convention              | Exact lock             | Consequence                                                                        |
| ----------------------- | ---------------------- | ---------------------------------------------------------------------------------- |
| Multiplicative interval | `Icc λ⁻¹ λ`            | The logarithmic image is exactly `Icc 0 L`.                                        |
| Log orientation         | `x = log (λ*u)`        | Lower endpoint maps to `0`, upper endpoint to `L`; the inverse is `exp x / λ`.     |
| Measure                 | `du/u` through `dStar` | The Jacobian is exactly absorbed; no residual factor remains.                      |
| Fourier normalization   | `(sqrt L)⁻¹`           | Every mode has norm one.                                                           |
| Phase                   | `exp(2*pi*I*n*x/L)`    | Integer-period endpoint cancellation is exact.                                     |
| Inner convention        | Antilinear first       | Pointwise exponent difference is `r - n`; coefficients later remain `inner V_n f`. |

The source document explicitly fixes all six conventions, including antilinearity in the first variable.  `[ABSTRACT][PAPER]`

## 7. K6 object precommit

Before implementation, record this immutable object:

```yaml
K6_OBJECT_PRECOMMIT:
  source_measure:
    dStar = volume.withDensity (fun u => ENNReal.ofReal u⁻¹)

  source_window:
    I_m i = Icc (lambda_m i)⁻¹ (lambda_m i)

  target_window:
    Icc 0 (L_m i)

  coordinate:
    x = Real.log (lambda_m i * u)

  inverse_coordinate:
    u = Real.exp x / lambda_m i

  normalized_mode:
    (Real.sqrt (L_m i))⁻¹ *
      Complex.exp
        (2 * Real.pi * Complex.I * n *
          (x / L_m i))

  inner_convention:
    conjugate_linear_first

  pointwise_inner_phase:
    r_minus_n

  output:
    Orthonormal ℂ (V_n_m i)

  forbidden_equivalents:
    - volume_without_u_inverse_density
    - log_u_div_lambda
    - target_interval_Icc_negL_zero
    - normalization_L_inverse
    - phase_n_minus_r_in_pointwise_inner
```

`[ABSTRACT][CONDITIONAL]`

No convention may be repaired after a plant result without opening a new named transaction.

## 8. Mandatory plants

### `P056L-1 — density/Jacobian plant`

Mutation:

```text
replace dStar.restrict (I_m i)
by volume.restrict (I_m i)
```

while retaining the same target Lebesgue integral.

Required result:

```text
G6_S2_LOG_WINDOW_DENSITY_MISMATCH
```

Without (du/u), the logarithmic Jacobian does not cancel.

### `P056L-2 — log orientation plant`

Mutation:

```text
log (u / lambda_m i)
```

instead of:

```text
log (lambda_m i * u).
```

Required result:

```text
G6_S2_LOG_WINDOW_ORIENTATION_MISMATCH
```

The mutated image is `Icc (-L_m i) 0`, not `Icc 0 (L_m i)`.

### `P056L-3 — endpoint/range plant`

Mutation:

```text
upper endpoint = (lambda_m i) ^ 2
```

or omit the lower reciprocal endpoint while retaining target `Icc 0 L`.

Required result:

```text
G6_S2_LOG_WINDOW_ENDPOINT_IMAGE_MISMATCH
```

This tests the full source window, not only its length.

### `P056L-4 — normalization plant`

Mutation:

```text
(L_m i)⁻¹
```

or `1` in place of:

```text
(Real.sqrt (L_m i))⁻¹.
```

Required result:

```text
G6_S2_V_MODE_UNIT_NORM_MISMATCH
```

The diagonal inner product no longer equals one.

### `P056L-5 — conjugation orientation plant`

Before integration, require a private pointwise helper whose exponent is literally `r - n`.

Mutation:

```text
r - n  →  n - r
```

Required result:

```text
G6_S2_V_MODE_INNER_CONJUGATION_MISMATCH
```

This plant is necessary because the final Kronecker-delta statement alone is insensitive to reversing the sign of the frequency difference.

## 9. Forbidden bundling

This transaction must not prove or define:

```text
orthogonal-projection reconstruction;
P_m_N finite Fourier sum;
projected coordinate = rawFplus;
full-object coordinate = Gwin;
D0PstarMuntzGalerkinResidualCrosswalkContract;
residual norm convergence;
compact-open residual decay;
Rminus or Rplus decay;
SlotS2.
```

It must not modify:

```text
D0KTrialStage1.lean
D0PstarMuntzCenteredCoordinateLock.lean
D0PstarMuntzGalerkinResidualContract.lean
Q3.Main
Goal 055
```

## 10. Direct downstream consumer and next decisive step

The one direct downstream consumer is:

```lean
theorem coe_P_m_N_apply_eq_sum_inner_V_n_m_smul
    (i : PairIndex) (f : H_m i) :
    ((P_m_N i f : E_m_N i) : H_m i) =
      ∑ n ∈ modeSet i,
        inner ℂ (V_n_m i n) f • V_n_m i n
```

`[ABSTRACT][CONDITIONAL]`

This theorem is **not authorized** in the selected transaction.

It is also the next cheapest decisive step. Once it is proved, the abstract orthogonal projection becomes the exact finite Fourier reconstruction needed to compare:

```text
gTrial_m_N
```

with:

```text
finiteLogFourierTrial
```

and hence with `rawFplus`.

## 11. Progress classification

This transaction is **PROOF_PROGRESS**, not merely representation progress.

It proves two unconditional source theorems:

1. the exact (du/u)-to-(dx) measure transport;
2. orthonormality of the literal production modes.

It does not merely declare a contract. It removes the first substantive premise from the full residual bridge.

It does **not** close the Phase-4B conditional crosswalk or compact-open decay.

## 12. Strongest attack

> Why publish a general measure-transport theorem instead of proving `V_n_m_orthonormal` directly and keeping the Jacobian calculation private?

Because the same measure transport is independently required later when converting an `H_m` residual coordinate into the literal `Gwin` integral. If the Jacobian and logarithmic orientation are hidden inside the orthonormality proof, the later bridge must reproduce them, creating a second opportunity for a C04 mismatch.

The source itself identifies the unitary logarithmic coordinate map as a canonical object. The proposed theorem materializes that object at integral level and immediately consumes it in `V_n_m_orthonormal`. It is therefore neither an orphan wrapper nor a future-budget name.

A second objection is:

> Orthonormality does not prove the projection reconstruction.

Correct. The success code says only measure transport and orthonormality. Projection reconstruction remains the sole next consumer.

## 13. Meta closeout

**What became smaller?**

The broad full-bridge program

```text
Fourier orthonormality
+ projection reconstruction
+ raw coordinate
+ Gwin coordinate
+ contract
```

is reduced to one exact first transaction:

```text
du/u logarithmic transport
→ V_n_m orthonormality.
```

**What was killed?**

* direct A as the best architecture;
* hiding the measure bridge inside an orthonormality-only proof;
* treating Mathlib projection API availability as proof of the weighted Fourier theorem;
* any claim that Phase 4B already supplies an object-first equality.

**What must not be tried again?**

Do not prove the same logarithmic Jacobian twice under slightly different phase or endpoint conventions.

**Current smallest named gap**

```text
G6_S2_D0_LOG_WINDOW_MEASURE_TRANSPORT_MISSING
```

**Next cheapest decisive step**

```text
coe_P_m_N_apply_eq_sum_inner_V_n_m_smul
```

**Registered prediction**

```text
P056L-A:
  the general measure-transport theorem and full-Z orthonormality
  compile in one bounded file without new project assumptions.

P056L-B:
  the first real API friction will be rewriting restricted withDensity
  and Lp representatives, not the Fourier integral.

P056L-C:
  after orthonormality, projection reconstruction will be a substantially
  smaller theorem than the later Gwin coordinate conversion.
```

**Fate of prior predictions**

```text
Phase-4B prediction:
  the full route begins with V_n_m orthonormality.
  CONFIRMED, but repaired one layer lower to expose the canonical
  logarithmic measure transport first.

Compact-open decay remains independent:
  CONFIRMED.
```

```yaml
iteration:
  target: G6_S2_FULL_L2_FOURIER_MELLIN_RESIDUAL_BRIDGE
  status: OPEN
  failed_strategy: prove_orthonormality_while_hiding_the_source_measure_transport
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: G6_S2_D0_LOG_WINDOW_MEASURE_TRANSPORT_MISSING
  invariant_learned: the same du_over_u logarithmic coordinate must drive Fourier orthonormality and the later Gwin residual coordinate
  forbidden_future_move: duplicate_the_logarithmic_change_of_variables_under_a_new_orientation
  next_decisive_test: coe_P_m_N_apply_eq_sum_inner_V_n_m_smul
  progress_class: PROOF_PROGRESS
  route_score: 5
```

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS:
  TRY_D0_LOG_WINDOW_MEASURE_TRANSPORT_AND_ORTHONORMALITY

TRANSACTION:
  G6_S2_D0_LOG_WINDOW_MEASURE_TRANSPORT_AND_ORTHONORMALITY

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: 1553624ae27944b93ef3adce265dc8e8e5c21b33
  expected_CODEX_CONTROL_sha256: fc77ff8d7483c87744f07e8aea3d59b08f9b5340541d3bf414885f239dfafc4e
  expected_phase4A_sha256: ce0226f7bd028449a04cae0dfa28e8998a0e835eba5ec0a56a93f0ae18b073a5
  expected_phase4B_sha256: 1f9b0f16210271fc699107f991a244421d98bbdafd695d5a585dae4aca4f73ff
  expected_mathlib_rev: 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67

CREATE:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0LogWindowMeasureTransport.lean

SOLE_IMPORT:
  Q3.Proofs.RouteB.D0KTrialStage1

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE:
  public_definitions: 0
  public_theorems: 2
  theorem_names:
    - integral_comp_logWindow_dStar
    - V_n_m_orthonormal

THEOREM_1:
  name: integral_comp_logWindow_dStar
  statement: |
    theorem integral_comp_logWindow_dStar
        (i : PairIndex) (F : ℝ → ℂ) :
        (∫ u : ℝ,
            F (Real.log (lambda_m i * u))
          ∂(dStar.restrict (I_m i))) =
          ∫ x : ℝ in Set.Icc 0 (L_m i), F x := by
      ...

THEOREM_2:
  name: V_n_m_orthonormal
  statement: |
    theorem V_n_m_orthonormal (i : PairIndex) :
        Orthonormal ℂ (V_n_m i) := by
      ...

PROOF_ROUTE:
  - prove lambda_m positivity and L_m positivity privately
  - prove the exact image of I_m under u ↦ log(lambda_m*u)
  - prove derivative u⁻¹ and monotonicity on I_m
  - rewrite dStar restriction through MeasureTheory.restrict_withDensity
  - use MeasureTheory.integral_withDensity_eq_integral_toReal_smul
  - use MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn
  - derive the unrestricted-integrand transport theorem
  - rewrite Lp inner products using MeasureTheory.L2.inner_def
  - expose MemLp.toLp representatives almost everywhere
  - prove the pointwise conjugation phase is r-n
  - consume the transport theorem
  - evaluate the finite exponential integral
  - close through orthonormal_iff_ite

K6_OBJECT_PRECOMMIT:
  source_window: Icc(lambda_m⁻¹, lambda_m)
  source_measure: du_over_u
  coordinate: log(lambda_m*u)
  target_window: Icc(0, L_m)
  mode_normalization: sqrt(L_m)⁻¹
  phase: 2*pi*I*n*x/L_m
  inner_convention: antilinear_first
  pointwise_frequency_difference: r_minus_n

MANDATORY_PLANTS:
  P056L_1_DENSITY:
    mutation: replace dStar by volume
    expected: G6_S2_LOG_WINDOW_DENSITY_MISMATCH

  P056L_2_LOG_ORIENTATION:
    mutation: replace log(lambda_m*u) by log(u/lambda_m)
    expected: G6_S2_LOG_WINDOW_ORIENTATION_MISMATCH

  P056L_3_ENDPOINT_IMAGE:
    mutation: alter one multiplicative-window endpoint while retaining Icc 0 L_m
    expected: G6_S2_LOG_WINDOW_ENDPOINT_IMAGE_MISMATCH

  P056L_4_NORMALIZATION:
    mutation: replace sqrt(L_m)⁻¹ by L_m⁻¹ or 1
    expected: G6_S2_V_MODE_UNIT_NORM_MISMATCH

  P056L_5_CONJUGATION:
    mutation: replace pointwise phase r-n by n-r
    expected: G6_S2_V_MODE_INNER_CONJUGATION_MISMATCH

VALIDATION:
  - verify all source hashes before edit
  - lake env lean q3.lean.aristotle/Q3/Proofs/RouteB/D0LogWindowMeasureTransport.lean
  - target lake build
  - full lake build
  - bash scripts/q3_check.sh q3.lean.aristotle/Q3/Proofs/RouteB/D0LogWindowMeasureTransport.lean
  - scan for sorry admit exact? native_decide axiom opaque Float
  - verify exactly two public theorems and zero public definitions
  - fire all five temporary mutations
  - remove all temporary mutation files
  - print axioms for both public theorems
  - require no axioms outside [propext, Classical.choice, Quot.sound]
  - strict Spine validation
  - proof database import
  - three SQLite integrity checks
  - git diff --check
  - exact git status report

STOP:
  G6_S2_D0_LOG_WINDOW_MEASURE_TRANSPORT_MISSING

SUCCESS:
  G6_S2_D0_LOG_WINDOW_TRANSPORT_AND_V_MODES_ORTHONORMAL_PROVED

DIRECT_DOWNSTREAM_CONSUMER_NOT_AUTHORIZED:
  name: coe_P_m_N_apply_eq_sum_inner_V_n_m_smul
  target_statement: |
    theorem coe_P_m_N_apply_eq_sum_inner_V_n_m_smul
        (i : PairIndex) (f : H_m i) :
        ((P_m_N i f : E_m_N i) : H_m i) =
          ∑ n ∈ modeSet i,
            inner ℂ (V_n_m i n) f • V_n_m i n

FORBIDDEN:
  - modify D0KTrialStage1.lean
  - modify Phase4A or Phase4B production files
  - prove projection reconstruction in this transaction
  - prove projected coordinate equals rawFplus
  - prove full-object coordinate equals Gwin
  - prove the residual crosswalk contract
  - prove residual decay or compact-open convergence
  - assert SlotS2
  - edit Q3.Main
  - edit Goal 055
  - create Bus 010
  - submit Aristotle
  - promote Route B
  - make PX or RH claim
  - open a fresh Proshka chat

PHASE:
  phase_key_change: false
  reuse_existing_chat: true

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  bus_010: VOID
  goal_055: HOLD
  aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
```
