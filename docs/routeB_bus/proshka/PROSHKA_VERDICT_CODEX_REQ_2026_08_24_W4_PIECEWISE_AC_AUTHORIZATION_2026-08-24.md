# STATUS: CONDITIONAL — TRY_W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEMMA
```yaml
PRIMARY: TRY_W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEMMA
PRIMARY_COUNT: 1

REQUEST:
  ID: REQ-2026-08-24-W4-PIECEWISE-AC
  PATH: docs/routeB_bus/CODEX_REQ_2026_08_24_W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY.md
  REQUEST_COMMIT: 42c23256dd5493c2ba85598ac611beb2ad7e0165
  REQUEST_FILE_BLOB: facfeae5bde395370e5371449d758733d23b0488
  REQUEST_PAYLOAD_AUTHORITATIVE: true
  SOURCE_COMMIT: 698e62522fafcb758e737643b1ec03cc2184b0b3
  PHASE_KEY_HASH: 1c0914e2e93a49defedf2c8a8497fbdc22de993b7404e0426e4b2d6c131f9aae
  BLOCKER_FINGERPRINT: 85280424cfb0e1bd5693d79ee77d9c3fcee1fe43691b30ee5c5dbfac4be76200

BASE_HEAD: 1d9548e4a2ca4e56b77a62a8e7a72202a9bcb6e4
VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_CODEX_REQ_2026_08_24_W4_PIECEWISE_AC_AUTHORIZATION_2026-08-24.md

TASK_ID: H2A_4_1B_3C_1_13A_W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEAN
MODE: CODEX_ONE_LEAN_NODE
LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean
LEAN_MODULE: Q3.Proofs.RouteB.G6N1SelectedFerrersPiecewiseACDerivativeIntegrability
ARISTOTLE: false

MATHEMATICAL_ADMISSION:
  exact_production_packet: ACCEPT
  complex_valued: PRESERVE
  full_endpoint_convention: PRESERVE
  global_absolute_continuity: REJECT
  seam_free_piecewise_absolute_continuity: ACCEPT
  derivative_integrability_on_each_piece: ACCEPT
  piecewise_integration_by_parts: SAME_NODE
  fixed_k_fourier_decay: SAME_NODE
  terminal_shifted_form_domain_membership: SUBSEQUENT_W4_ASSEMBLY
  w3_l2_implies_shifted_domain: false
  uniform_in_k_rate: false

PUBLIC_SURFACE:
  DEFINITIONS:
    - selectedFerrersAbelLogRepresentative
    - selectedFerrersAbelLogZeroExtension
    - selectedFerrersAbelLogSeamFreeOn
    - selectedFerrersAbelLogDerivativeBudget
    - selectedFerrersAbelLogJumpBudget
  THEOREMS:
    - selectedFerrersLemma73SourcePacket_absolutelyContinuousOnInterval
    - selectedFerrersAbelLogRepresentative_absolutelyContinuousOnInterval_of_seamFree
    - selectedFerrersAbelLogRepresentative_intervalIntegrable_deriv_of_seamFree
    - selectedFerrersAbelLogZeroExtension_fourier_decay_off_zero
    - selectedFerrersAbelLogZeroExtension_fourier_decay

CLOSES:
  - W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEMMA
  - W4_LOG_COORDINATE_FINITE_JUMP_FOURIER_DECAY
OPENS:
  - W4_FIXED_K_SHIFTED_FORM_DOMAIN_ASSEMBLY
NEXT_LOAD_BEARING_GAP: W4_FIXED_K_SHIFTED_FORM_DOMAIN_ASSEMBLY

SCOPE: ABSTRACT
VERIFIER: CONDITIONAL_LEAN_PENDING
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
W5_COFINAL_RATE: OUTSIDE_TRANSACTION

EXPECTED_AXIOM_PROFILE:
  - propext
  - Classical.choice
  - Quot.sound

ARSENAL_MANDATE:
  ACCEPTED: true
  EFFECT_ON_THIS_NODE: NONE
ARSENAL_CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C13_RESTORE_SYMMETRY_BY_EXPLICIT_SHADOW

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
```

## ROUTE MAP

The candidate survives the exact-object audit.

The exact packet

```lean
selectedFerrersLemma73SourcePacket k
```

is not an arbitrary bounded-variation function.  In the kernel-green W2 source,
the selected coefficient rows satisfy the polynomially weighted summability

\[
\sum_{q\ge 0}(q+1)^2|a_q|<\infty,
\]

and the closed Legendre derivative majorant gives a finite Lipschitz constant on
the exact closed physical window.  The proof keeps the complex source scale and
the production endpoint values.  Therefore the packet is absolutely continuous
on that closed physical window. `[ABSTRACT][PAPER]`

For fixed `k`, compact support makes the starred sum finite on the exact selected
window.  Away from the finitely many equations

\[
n\,u=\lambda_k,
\]

the active index set is constant.  On each such component,

\[
u=\exp(x)/\lambda_k
\]

turns the exact full-endpoint Abel limit into a finite sum of absolutely
continuous complex-valued terms, plus the smooth half-center shadow.  Its
derivative is interval-integrable. `[ABSTRACT][PAPER]`

The global direct representative is not absolutely continuous: its additive
zero extension has two endpoint jumps, and the full-endpoint `E_star` convention
has finitely many internal jumps.  The correct conclusion is piecewise absolute
continuity plus an explicit finite jump ledger, never global absolute
continuity. `[ABSTRACT][PAPER]`

### Decisive source/API finding

The W2 declarations

```text
selected_weighted_summable
normalizedPhysicalMode_lipschitz_on_window
selectedPacket_lipschitz_on_window
```

and the W3 declarations

```text
selectedSeamSet
selectedPeriodization_continuousAt_zero_off_seams
selectedPeriodization_continuousAt_one_off_seams
```

are `private`.  They are valid proof blueprints, not callable imported APIs.
The new file must reconstruct the required public certificate from the public
tail-splice, derivative-series, support, and selected-pair suppliers.  It must
not cite a private declaration as if it were available across modules.
`[ABSTRACT][LEAN]`

A second API guard is load-bearing: the convenient pinned
`AbsolutelyContinuousOnInterval.intervalIntegrable_deriv` surface is not to be
assumed to solve the complex-valued case automatically.  Prove complex
derivative integrability directly from the explicit derivative majorant, or
prove it componentwise and reassemble the complex function.  Taking only a real
part is not an admissible surrogate. `[ABSTRACT][CONDITIONAL]`

## EXACT LEAN THEOREM PACKET

The following declarations are frozen.  Cosmetic line wrapping is permitted;
source object, quantifiers, conclusions, and Fourier normalization are not.

```lean
noncomputable def selectedFerrersAbelLogRepresentative
    (k : ℕ) : ℝ → ℂ :=
  fun x =>
    selectedFerrersAbelLimit k
      (Real.exp x /
        lambda_m (selectedFerrersPreAnchorIndex k))

noncomputable def selectedFerrersAbelLogZeroExtension
    (k : ℕ) : ℝ → ℂ :=
  Set.indicator
    (Set.Icc 0 (L_m (selectedFerrersPreAnchorIndex k)))
    (selectedFerrersAbelLogRepresentative k)

/-- A compact additive-log interval lies in the exact selected window and
contains no production seam `n * exp(x) / lambda_k = lambda_k`. -/
def selectedFerrersAbelLogSeamFreeOn
    (k : ℕ) (a b : ℝ) : Prop :=
  Set.uIcc a b ⊆
      Set.Icc 0 (L_m (selectedFerrersPreAnchorIndex k)) ∧
    ∀ n : ℕ+, ∀ x ∈ Set.uIcc a b,
      (((n : ℕ) : ℝ) *
          (Real.exp x /
            lambda_m (selectedFerrersPreAnchorIndex k))) ≠
        lambda_m (selectedFerrersPreAnchorIndex k)

theorem selectedFerrersLemma73SourcePacket_absolutelyContinuousOnInterval
    (k : ℕ) :
    AbsolutelyContinuousOnInterval
      (selectedFerrersLemma73SourcePacket k)
      (-(selectedFerrersPreAnchorPair k).pw.lambda)
      (selectedFerrersPreAnchorPair k).pw.lambda

theorem
    selectedFerrersAbelLogRepresentative_absolutelyContinuousOnInterval_of_seamFree
    (k : ℕ) {a b : ℝ}
    (hfree : selectedFerrersAbelLogSeamFreeOn k a b) :
    AbsolutelyContinuousOnInterval
      (selectedFerrersAbelLogRepresentative k) a b

theorem
    selectedFerrersAbelLogRepresentative_intervalIntegrable_deriv_of_seamFree
    (k : ℕ) {a b : ℝ}
    (hfree : selectedFerrersAbelLogSeamFreeOn k a b) :
    IntervalIntegrable
      (deriv (selectedFerrersAbelLogRepresentative k)) volume a b
```

The derivative and jump budgets must be exact fixed-`k` objects.  The internal
seams are

\[
x_n=\log((k+2)/n),\qquad 2\le n\le k+1.
\]

The jump budget contains exactly:

1. the zero-extension jump at `x = 0`;
2. the zero-extension jump at `x = L_m (selectedFerrersPreAnchorIndex k)`;
3. for every internal `n`, the full-endpoint jump contributed by
   `selectedFerrersLemma73SourcePacket k` at `lambda_m`;
4. no jump from the half-center shadow, which is continuous.

The definitions may use an equivalent finite-sum normal form, but must reduce to
this ledger:

```lean
noncomputable def selectedFerrersAbelLogDerivativeBudget
    (k : ℕ) : ℝ :=
  ∫ x : ℝ in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
    ‖deriv (selectedFerrersAbelLogRepresentative k) x‖

noncomputable def selectedFerrersAbelLogJumpBudget
    (k : ℕ) : ℝ :=
  ‖selectedFerrersAbelLogRepresentative k 0‖ +
  ‖selectedFerrersAbelLogRepresentative k
      (L_m (selectedFerrersPreAnchorIndex k))‖ +
  ∑ n ∈ Finset.Icc 2 (k + 1),
    ‖((Real.sqrt
        (lambda_m (selectedFerrersPreAnchorIndex k) / (n : ℝ)) : ℝ) : ℂ) *
      selectedFerrersLemma73SourcePacket k
        (lambda_m (selectedFerrersPreAnchorIndex k))‖
```

If elaboration requires a syntactically different but propositionally equal
finite sum, prove and print the equality; do not silently change the ledger.

The same node must finish the hand-written complex piecewise integration by
parts.  With Mathlib's Fourier convention `exp (-2*pi*i*x*t)`, the public
estimate is:

```lean
theorem selectedFerrersAbelLogZeroExtension_fourier_decay_off_zero
    (k : ℕ) {t : ℝ} (ht : t ≠ 0) :
    ‖𝓕 (selectedFerrersAbelLogZeroExtension k) t‖ ≤
      (selectedFerrersAbelLogDerivativeBudget k +
        selectedFerrersAbelLogJumpBudget k) /
      (2 * Real.pi * |t|)

theorem selectedFerrersAbelLogZeroExtension_fourier_decay
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ,
        ‖𝓕 (selectedFerrersAbelLogZeroExtension k) t‖ ≤
          C / (1 + |t|)
```

This is the exact fixed-`k` conclusion.  It is not a uniform family estimate.
The quantifier spine is

```text
forall k, exists C_k, forall t, ...
```

and never

```text
exists C, forall k, forall t, ...
```

### Downstream theorem that spends this node

The following theorem belongs to the subsequent W4 assembly file

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
G6N1SelectedFerrersFixedKShiftedRootEnergy.lean
```

and is not authorized for implementation before this node is kernel-green:

```lean
noncomputable def selectedFerrersAbelLimitHm
    (k : ℕ) : H_m (selectedFerrersPreAnchorIndex k) :=
  (selectedFerrersAbelLimit_memLp k).toLp
    (selectedFerrersAbelLimit k)

theorem selectedFerrersAbelLimit_mem_sourceArchimedeanShiftedFormDomain
    (k : ℕ) :
    selectedFerrersAbelLimitHm k ∈
      sourceArchimedeanShiftedFormDomain
        (selectedFerrersPreAnchorIndex k)
```

That downstream proof must separately establish the a.e. provenance between
`selectedFerrersAbelLogZeroExtension k` and
`sourceLogWindowZeroExtension ... (selectedFerrersAbelLimitHm k)`, then use the
already-proved ordinary-Fourier/synthesized-isometry crosswalk.  Absolute
continuity is proved only for the direct representative; it is not transported
through a.e. equality.

## REQUIRED IMPORTS AND EXISTING SUPPLIERS

### Direct imports

```lean
import Q3.Proofs.RouteB.G6N1SelectedFerrersAbelPoissonL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
```

Do not import the global Fourier derivative theorem as an engine.

### Public source suppliers

```text
selectedFerrersLemma73SourcePacket
selectedFerrersLemma73SourcePacket_boundedVariationOn
mode4OrdinaryLegendrePolynomial_derivative_abs_le_closed
mode4RecurrenceRow_polynomiallyWeighted_abs_summable_of_tail_splice
Mode4FerrersRegularEvenProlateSolution.ferrersSeries_hasDerivAt_firstDerivativeSeries
selectedFerrersPreAnchorSeparation
selectedFerrersAbelLimit
selectedFerrersAbelLimit_memLp
selectedFerrersPreAnchorIndex
lambda_m
L_m
I_m
```

`selectedFerrersLemma73SourcePacket_boundedVariationOn` is a control and a
source lock.  It is not a proof of absolute continuity.

### Downstream-only suppliers

```text
sourceLogWindowZeroExtension
coeFn_sourceLogWindowFourierL2Isometry_eq_fourier_sourceLogWindowZeroExtension
mem_sourceArchimedeanShiftedFormDomain_iff
sourceArchimedeanShiftedSqrtWeight
```

## PROOF ORDER

1. Rebuild, in the new file, a public weighted-summability certificate for the
   two selected regular-even solutions from the public tail-splice theorem.
   Do not call W2's private helper.
2. Rebuild the closed physical-window derivative bound and Lipschitz estimate
   for the exact complex-scaled packet.  Convert the resulting
   `LipschitzOnWith` statement with
   `LipschitzOnWith.absolutelyContinuousOnInterval`.
3. Prove the fixed active-index lemma on the selected multiplicative window:
   compact support reduces `E_star` to the positive indices `1 <= n <= k+2`.
4. Introduce the direct additive-log representative and the exact seam-free
   predicate above.
5. On a seam-free interval, prove that every active packet term remains wholly
   inside or wholly outside the physical support.  Assemble the finite sum,
   the `sqrt` factor, the `exp/lambda` transport, and the half-center shadow.
6. Prove complex derivative interval-integrability from the explicit derivative
   majorant.  If the pinned generic derivative-integrability lemma is
   real-valued, split into real and imaginary components and reassemble; do not
   weaken the source to a real-valued packet.
7. Order the explicit seams `log((k+2)/n)`, perform integration by parts on the
   open components with one-sided endpoint representatives, and telescope.
   Keep the exact production full-endpoint values as the jump terms.
8. Combine the off-zero `1/|t|` estimate with the ordinary `L1` Fourier bound
   near `t=0` to obtain `C_k/(1+|t|)`.
9. Print axioms for every public declaration and every local plant.

## MANDATORY PLANTS

The new file must contain and print axioms for these local plants:

```text
boundedVariation_without_absoluteContinuity_plant
  A one-jump step function is BV but not absolutely continuous.

ae_equal_representatives_can_disagree_on_absoluteContinuity_plant
  A zero function and a function changed at one point are a.e. equal, while
  only the exact pointwise representative is continuous/AC.

global_absolute_continuity_fails_for_finite_jump_sources_plant
  Piecewise AC plus finite jumps must not elaborate into global AC.

fixed_k_decay_does_not_supply_uniform_family_rate_plant
  A family can have one decay constant for each k with no uniform constant.
```

The following earlier guards remain binding and must be cited in the source
record rather than reinterpreted:

```text
L2_WITHOUT_LOG_WEIGHTED_ENERGY
FULL_ENDPOINT_VS_MIDPOINT_SEAM
ORDINARY_FOURIER_VS_SYNTHESIZED_ISOMETRY
FIXED_K_FINITE_NOT_COFINAL_RATE
```

## VALIDATION COMMANDS

```text
WORKDIR: q3.lean.aristotle
  lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean

WORKDIR: q3.lean.aristotle
  lake build Q3.Proofs.RouteB.G6N1SelectedFerrersPiecewiseACDerivativeIntegrability

WORKDIR: repository root
  scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean
```

Every printed declaration must have exactly the expected standard profile:

```text
[propext, Classical.choice, Quot.sound]
```

Any `sorryAx`, new axiom, hidden constant, weakened seam hypothesis, or changed
endpoint representative returns:

```text
W4_PIECEWISE_AC_DERIVATIVE_NODE_KERNEL_OR_SEMANTIC_GAP
```

If the exact packet derivative cannot be made interval-integrable on one
seam-free compact interval after the public weighted-summability supplier has
been reconstructed, return:

```text
W4_EXACT_PACKET_DERIVATIVE_AC_FATAL
```

Do not respond by changing the packet.

## SEMANTIC ADMISSION AND PROVENANCE

The node is admitted only under all of the following locks:

```text
source packet:
  selectedFerrersLemma73SourcePacket k

target multiplicative representative:
  selectedFerrersAbelLimit k

additive coordinate:
  x = log(lambda_m i * u)
  u = exp(x) / lambda_m i

selected index:
  i = selectedFerrersPreAnchorIndex k

selected window:
  x in [0, L_m i]
  u in I_m i

endpoint convention:
  production full endpoint values

shadow:
  +(1/2) * selectedFerrersLemma73SourcePacket k 0 * sqrt(u)

scalar category:
  complex-valued throughout

Fourier provenance:
  ordinary Fourier decay is proved for the direct representative;
  synthesized-isometry transfer is only a.e. and is spent downstream

scope:
  fixed k only
```

Source receipts:

```text
W2 source blob:
  0c57204461353f16ed91f1240173c90f94ad1b4d

W3 source blob:
  a064544af242608b8d09b94931412d1bccd5c392

W3 verdict blob:
  82d0b583f540afc7985b149f4a774bfda48997d1

W4 preflight blob:
  f3107d15c4598365d8e9824a61fc29ec8c7773f1
```

## FORBIDDEN SHORTCUTS

- Do not replace the production full-endpoint packet by a midpoint, continuous,
  or mollified representative.
- Do not infer absolute continuity from bounded variation.
- Do not infer pointwise absolute continuity from an a.e. equality of `Lp`
  representatives.
- Do not call private W2/W3 declarations from the new module.
- Do not apply Mathlib's global `fourier_deriv` theorem to the jumping source.
- Do not discard the imaginary part or prove only a real-valued surrogate.
- Do not infer shifted form-domain membership from W3 `L2` convergence.
- Do not turn `forall k, exists C_k` into a uniform-in-`k` estimate.
- Do not perform W5 cofinal-rate work in this transaction.
- Do not edit any historical pushed artifact.
- Do not modify `Q3.Main`, route state, `BUS_010`, or any RH export.

## FINAL PROPOSAL

Authorize exactly the Lean node above.  The integration-by-parts theorem belongs
in the same node because it is the cheapest decisive test that the complex
piecewise derivative and the exact full-endpoint jump ledger actually produce
the claimed Fourier decay.  Deferring it would let a merely local AC wrapper
pass while the load-bearing Fourier estimate remained untested.

The subsequent W4 assembly is limited to:

```text
direct representative decay
+ a.e. source-representative provenance
+ ordinary-Fourier/synthesized-isometry crosswalk
+ exact logarithmic symbol domination
-> selectedFerrersAbelLimitHm in sourceArchimedeanShiftedFormDomain
```

No cofinal statement follows.

## STRONGEST ATTACK

The strongest objection is category mismatch:

> Absolute continuity is pointwise-representative-sensitive, while `H_m`, the
> synthesized Fourier isometry, and its crosswalk are a.e.-equivalence objects.

This objection is valid and is why the proof is split in the stated order.
First prove piecewise AC and Fourier decay for the direct exact representative.
Only afterward transfer the ordinary Fourier integral through an a.e. equality.
At no point may an a.e. equality be used to transport absolute continuity.

The second objection is that the currently visible derivative and seam helpers
are private.  This is an API cost, not a mathematical supplier.  The new file
must rebuild a public exact certificate from the public lower-level theorems.
If that rebuild fails because a supposedly public lower-level theorem is absent,
report the exact missing theorem; do not weaken the target.

## CODEX DIRECTIVE

```text
Execute only:
  H2A_4_1B_3C_1_13A_W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEAN

Create exactly:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean

Ship the Lean source and its SOURCE RECORD in one commit under the shared
supplier contract.  Do not start the downstream shifted-domain assembly.
Stop on the first source-object, private-API, complex-derivative, seam-order,
or jump-ledger mismatch and report the smallest exact missing lemma.
```

## META CLOSEOUT

**What became smaller?**

The W4 wall is now one kernel-bounded node with an exact direct representative,
exact seam predicate, exact derivative/jump budgets, and exact Fourier-decay
output.

**What was killed?**

- global absolute continuity of the production zero extension;
- BV as a substitute for AC;
- a.e. equality as a transport rule for AC;
- the assumption that private W2/W3 helpers are imported APIs;
- any W3-`L2` to shifted-domain implication.

**What must not be tried again?**

Global smooth Fourier differentiation, midpoint replacement, real-valued
projection, and uniform-in-`k` strengthening.

**Current smallest named gap?**

```text
W4_FIXED_K_SHIFTED_FORM_DOMAIN_ASSEMBLY
```

**Next cheapest decisive test?**

Run the three validation commands on the exact node and inspect the first
private-API or complex-derivative normal-form failure before any downstream
work.

**Fate of prior registered predictions**

```text
P_W4_1:
  CONFIRMED_AT_PAPER_AND_SOURCE_LEVEL.
  Exact fixed-k direct representative is piecewise AC with finitely many jumps;
  kernel theorem still pending.

P_W4_2:
  CONFIRMED_CONDITIONALLY.
  One piecewise IBP gives the required fixed-k 1/(1+|t|) decay if the exact
  derivative/jump ledger compiles.

P_W4_3:
  CONFIRMED.
  No uniform-in-k or cofinal rate follows.
```

**Predictions registered before the Lean test**

```text
P_W4_AC_LEAN_1:
  p = 0.72
  The frozen public theorem packet compiles without statement weakening.

P_W4_AC_LEAN_2:
  p = 0.84
  The first failure, if any, is private-supplier reconstruction or
  complex-derivative API shape, not a counterexample to piecewise AC.

P_W4_AC_LEAN_3:
  p = 0.96
  A green node has exactly the standard axiom triple.
```

**Memory entry**

```yaml
iteration: W4_piecewise_AC_authorization
target: W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEMMA
status: OPEN_AUTHORIZED
failed_strategy: global_fourier_deriv_on_jumping_source
cognitive_operator_used: MINIMAL_LEMMA
new_gap_name: W4_FIXED_K_SHIFTED_FORM_DOMAIN_ASSEMBLY
invariant_learned: pointwise_AC_and_ae_Fourier_crosswalk_must_be_spent_in_that_order
forbidden_future_move: transport_AC_through_ae_or_replace_full_endpoint_representative
next_decisive_test: compile_exact_piecewise_AC_and_jump_IBP_node
```
