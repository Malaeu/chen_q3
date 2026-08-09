# STATUS: OPEN — B3.0P QUOTIENT-SAFE SHIFTED ARCHIMEDEAN FORM-DOMAIN SUBMODULE PREFLIGHT SELECTED; PRODUCTION FORBIDDEN

```yaml
STATUS: OPEN

PRIMARY: TRY_GOAL057_B3_0P_SHIFTED_ARCH_FORM_DOMAIN_SUBMODULE_PREFLIGHT
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_GOAL057_B3_0P_SHIFTED_ARCH_FORM_DOMAIN_SUBMODULE_PREFLIGHT
OPERATIVE_CLASS_COUNT: 1

BINARY_RULING:
  NEXT_CHILD_SELECTED: true
  NEXT_CHILD_ID: GOAL057_B3_0P_SHIFTED_ARCH_FORM_DOMAIN_SUBMODULE
  AUTHORIZATION_SCOPE: UNTRACKED_EXACT_LEAN_PREFLIGHT_ONLY
  PRODUCTION_AUTHORIZED: false
  TRACKED_REPOSITORY_MUTATION_AUTHORIZED: false
  ROUTE_STATE_MUTATION_AUTHORIZED: false
  SUCCESSOR_AFTER_B3_0P_SELECTED: false
  SUCCESSOR_AFTER_B3_0P_AUTHORIZED: false

NO_PRODUCTION_AUTHORIZATION_IN_THIS_VERDICT: true

TRANSACTION:
  ID: GOAL057_B3_0P_SHIFTED_ARCH_FORM_DOMAIN_SUBMODULE_PREFLIGHT
  MODE: UNTRACKED_EXACT_LEAN_PREFLIGHT
  SAME_LIVING_CHAT: true
  PHASE_KEY_CHANGE: false
  ARISTOTLE_SUBMISSION: NONE

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean

  CONTROLLING_REQUEST:
    path: PROSHKA_REQUEST_GOAL057_B3_0_POST_O_NEXT_NODE_ADJUDICATION_2026-08-09.txt
    observed_sha256: 393c877b44ba5e0e8cc87ad1a86878a8d641313ef4d4d0eabcf309705595e59e
    observed_bytes: 12664
    observed_wc_lines: 343
    final_LF: true
    utf8: PASS
    read_byte_for_byte: true
    status: PASS

  HEAD:
    expected: ce02a74715282a46ae95ff6fc22de7e578ee7bd1
    observed_origin_rh_clean: ce02a74715282a46ae95ff6fc22de7e578ee7bd1
    status: PASS

  EXECUTION_STATE:
    declared_sha256: d2621774f121c35534dd4df4c1af1222598c3851cd0a869d7e6dd29ccf3293ee
    content_at_pin_verified: true
    independent_sha256_rehash_by_judge: false
    stage: RB-GOAL-057-B3-0O-CLOSED
    obligation: GOAL057_B3_0_POST_O_NEXT_NODE_ADJUDICATION
    status: OPEN_ADJUDICATION_REQUIRED_NO_SUCCESSOR_AUTHORIZED

  ROUTE_STATE:
    declared_sha256: eb029b01e52eb1b7dc9381039c1ee1525f7025b0834242836a5367469984e05e
    independent_sha256_rehash_by_judge: false

  UNRELATED_STAGED_PATCH:
    expected_sha256: 291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b
    preflight_recheck_required: true
    preservation_required: true

CLOSED_PARENT:
  ID: B3_0O
  FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarShiftedArchSqrtWeight.lean
  SHA256: b1641e36554b66131bb04b14b606b94557a8f004a686fad73b51378e72360bba
  STATUS: CLOSED
  REOPENED: false

SELECTED_CHILD:
  ID: GOAL057_B3_0P_SHIFTED_ARCH_FORM_DOMAIN_SUBMODULE
  EXACT_MEANING_OF_B3_0P: SHIFTED_ARCH_FORM_DOMAIN_SUBMODULE
  SCOPE: ABSTRACT
  VERIFIER: CONDITIONAL_UNTIL_EXACT_LEAN_PREFLIGHT
  PROGRESS_CLASS: REPRESENTATION_PROGRESS
  COGNITIVE_OPERATOR: MINIMAL_LEMMA
  ROUTE_SCORE: 5

SCRATCH_PATH:
  q3.lean.aristotle/Goal057B3_0P_ShiftedArchFormDomain_Scratch.lean

FUTURE_PRODUCTION_PATH_NOT_AUTHORIZED:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarShiftedArchFormDomain.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarShiftedArchSqrtWeight
  - Q3.Proofs.RouteB.D0PstarSourceLogWindowFourierL2Isometry

NAMESPACE:
  Q3.RouteB.D0Pstar

CANDIDATE:
  filename: GOAL057_B3_0P_SHIFTED_ARCH_FORM_DOMAIN_SUBMODULE_PREFLIGHT_CANDIDATE_2026-08-09.lean
  sha256: d2fc68954ae6604d1573bbe37b83e08577f60f4d39f5b9b9f3548821ce866a50
  bytes: 2845
  wc_lines: 78
  final_LF: true
  forbidden_token_matches: 0
  judge_reran_Lean: false
  status: EXACT_BYTES_PINNED_REQUIRES_DIRECT_LEAN

PUBLIC_SURFACE_CEILING:
  definitions:
    - sourceArchimedeanShiftedFormDomain
  theorems:
    - mem_sourceArchimedeanShiftedFormDomain_iff
  total_public_declarations: 2

PRIVATE_SURFACE_CEILING:
  definitions:
    - sourceArchimedeanShiftedWeightedImage
  theorems: []
  total_private_declarations: 1

SEMANTIC_CONTRACT:
  domain_carrier: Submodule_C_of_H_m_i
  membership: sqrt_shifted_arch_weight_times_B3_0L_image_is_MemLp_2_volume
  representative_safety: AE_EQ_QUOTIENT_SAFE
  exact_form_weight: sourceArchimedeanShiftedSqrtWeight
  exact_transform: sourceLogWindowFourierL2Isometry
  arbitrary_vector_pointwise_Fourier_claim: false
  full_shift_operator_domain_claim: false
  literal_mode_membership_claim: false
  finite_mode_span_inclusion_claim: false
  density_claim: false
  form_definition_claim: false
  closedness_claim: false
  D0_2_equality_claim: false
  associated_operator_claim: false

PREFLIGHT_STOP:
  GOAL057_B3_0P_SHIFTED_ARCH_FORM_DOMAIN_SUBMODULE_PREFLIGHT_FAILED

SPECIFIC_STOPS:
  - GOAL057_B3_0P_LP_QUOTIENT_REPRESENTATIVE_API_GAP
  - GOAL057_B3_0P_MEMLP_SUBMODULE_CLOSURE_API_GAP
  - B3_0P_FORM_OPERATOR_WEIGHT_COLLAPSE
  - B3_0P_ARBITRARY_VECTOR_WEIGHTED_DOMAIN_OVERCLAIM
  - SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION
  - B3_0P_FINITE_RIESZ_SUBSTITUTED_FOR_AMBIENT_FORM_DOMAIN
  - ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK
  - B3_0P_SCOPE_SMUGGLE

PREFLIGHT_SUCCESS:
  GOAL057_B3_0P_SHIFTED_ARCH_FORM_DOMAIN_SUBMODULE_PREFLIGHT_PROVED

NEXT_GAP_NOT_AUTHORIZED:
  GOAL057_B3_0Q_LITERAL_MODE_IN_SHIFTED_ARCH_FORM_DOMAIN

CHECKPOINT_EFFECT:
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  effect_after_preflight_success: STRICTLY_ADVANCED_NOT_CLOSED
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10

ARSENAL:
  MANDATE_ACCEPTED: true
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

FINAL_BOUNDARY:
  ROUTE: CHALLENGER_NOT_RH
  ACTIVE_BUS_GOAL: 057
  BUS_010: VOID
  GOAL_055: HOLD
  G2_CCM: FROZEN
  H4A1B: OPEN
  ARISTOTLE_SUBMISSION: NONE
  ROUTE_PROMOTION: false
  PX_RH_CLAIM: NOT_MADE
  SOLE_OWNER_GATE: PX_RH_CLAIM
```

## 1. Source-lock ruling

The controlling request was read byte-for-byte. Its actual lock is SHA-256 `393c877b…e59e`, 12,664 bytes, 343 `wc` lines, valid UTF-8, and final LF. It fixes B3.0O as closed, B3.0 as open, the current checkpoint as advanced but not closed, and explicitly forbids production authorization here.  `[ABSTRACT][PAPER]`

The live `rh_clean` state is exactly commit `ce02a74715282a46ae95ff6fc22de7e578ee7bd1`. The physical execution state records:

```text
RB-GOAL-057-B3-0O-CLOSED
GOAL057_B3_0_POST_O_NEXT_NODE_ADJUDICATION
OPEN_ADJUDICATION_REQUIRED_NO_SUCCESSOR_AUTHORIZED
```

and preserves the coarse ledger at `0 closed / 10 remaining`.   `[ABSTRACT][PAPER]`

B3.0O is present at that pin and exposes exactly the globally nonnegative square-root weight, continuity, measurability, nonnegativity, and the exact square identity. It defines no domain, form, graph, or operator.  `[ABSTRACT][LEAN]`

## 2. Operative ruling

[
\boxed{
\texttt{TRY_GOAL057_B3_0P_SHIFTED_ARCH_FORM_DOMAIN_SUBMODULE_PREFLIGHT}
}
]

Candidate **B** is selected.

B3.0P is fixed to mean:

```text
the exact complex Submodule of H_m i consisting of vectors whose B3.0L
whole-line image becomes L² after multiplication by the B3.0O
square-root weight.
```

No standalone predicate object is selected. The predicate appears internally as the carrier of the selected `Submodule` and publicly through one membership theorem.

## 3. Exact pinned-Mathlib API ruling

The quotient-safe construction is executable from the pinned Mathlib v4.26.0 APIs.

The required closure tools already exist:

```lean
MemLp.add
MemLp.const_smul
MemLp.ae_eq

Lp.coeFn_zero
Lp.coeFn_add
Lp.coeFn_smul
```

`MemLp.add` provides finite-(L^p) closure under addition.  `[ABSTRACT][LEAN]`

`MemLp.const_smul` provides closure under complex scalar multiplication.  `[ABSTRACT][LEAN]`

`MemLp.ae_eq` transfers membership across an almost-everywhere equality, while `Lp.coeFn_zero/add/smul` expose the quotient operations only almost everywhere rather than pretending they are pointwise definitional equalities.   `[ABSTRACT][LEAN]`

Therefore the correct construction is not:

```text
choose an arbitrary representative of the Lp class;
multiply pointwise;
hope the result is independent of the choice.
```

It is:

```text
use the existing Lp coercion;
state MemLp of the weighted coercion;
prove Submodule closure through the official a.e. coercion laws;
transport MemLp through MemLp.ae_eq.
```

Because the B3.0O weight is an ordinary finite real-valued function, multiplying two representatives that agree almost everywhere preserves their almost-everywhere equality. No `∞ · 0` ambiguity is introduced. `[ABSTRACT][LEAN]`

## 4. Candidate comparison

| Candidate                                           | Actual wall reduction                                                                              |                                    Cost | Ruling                                                                               |
| --------------------------------------------------- | -------------------------------------------------------------------------------------------------- | --------------------------------------: | ------------------------------------------------------------------------------------ |
| **A — standalone predicate**                        | Merely names the carrier condition; proves no linear category                                      |                                     Low | **Killed as standalone public scaffolding.** Its content is folded into B. **[C10]** |
| **B — exact `Submodule ℂ (H_m i)`**                 | Creates the lawful form-domain carrier and proves zero/add/smul closure through a.e. quotient laws | Low–medium; exact compile cost unproved | **Selected**                                                                         |
| **C — every literal mode lies in the domain**       | First analytic inhabitance theorem; consumes B3.0B3 and the B3.0L mode-image law                   |                                  Medium | Retained as B3.0Q, not authorized                                                    |
| **D — finite mode span inclusion**                  | Converts C plus Submodule closure into `E_m_N`/finite-synthesis inclusion                          |                      Low–medium after C | Retained separately                                                                  |
| **E — density**                                     | Uses the complete literal basis after C/D                                                          |                                  Medium | Retained; not bundled                                                                |
| **F — shifted multiplication form**                 | Defines the form only after a lawful carrier exists                                                |                             Medium–high | Later                                                                                |
| **G — ambient W02 extension**                       | Independent bounded rank-two perturbation wall                                                     |               Medium–high, cost unknown | Not selected                                                                         |
| **H — ambient Prime extension**                     | Independent finite sum of bounded source shifts                                                    |                      High, cost unknown | Not selected                                                                         |
| **I — carrier/core/density/form/closedness bundle** | Bundles several independent analytic walls                                                         |                                    High | **Killed as current overbundle**                                                     |

`[ABSTRACT][CONDITIONAL]`

## 5. Answers to the mandatory API and mathematical questions

### 5.1 Exact representative-safe API

The selected domain is defined directly on `x : H_m i` by applying the released linear isometry

```lean
sourceLogWindowFourierL2Isometry i x :
  Lp ℂ 2 volume
```

and testing `MemLp` after multiplication by the released real square-root weight.

B3.0L is defined on all of `H_m i`; it only withholds an arbitrary-vector **pointwise classical Fourier interpretation**. That nonclaim does not prevent use of the `Lp` object itself.  `[ABSTRACT][LEAN]`

No existing global multiplication operator is needed at this stage. The domain is the pullback of a weighted-`MemLp` condition, packaged directly as a source-space `Submodule`.

### 5.2 Is Candidate A load-bearing?

No.

A public definition

```lean
def shiftedArchDomainPredicate (i) (x) : Prop := MemLp ...
```

would only name the carrier condition. Candidate B can prove the exact `Submodule` in the same bounded file using existing APIs. A separate predicate would create a duplicate interface and would not close the category wall.

The selected public membership theorem already exposes the exact predicate for downstream rewriting.

### 5.3 Exact declaration surface

Public:

```lean
sourceArchimedeanShiftedFormDomain
    (i : PairIndex) : Submodule ℂ (H_m i)

mem_sourceArchimedeanShiftedFormDomain_iff
    (i : PairIndex) (x : H_m i) :
    x ∈ sourceArchimedeanShiftedFormDomain i ↔ MemLp ...
```

Private:

```lean
sourceArchimedeanShiftedWeightedImage
    (i : PairIndex) (x : H_m i) : ℝ → ℂ
```

No public predicate alias, form, density theorem, operator domain, or source-form identification is included.

### 5.4 Can B3.0B3 later prove literal-mode membership?

Yes, but only as a separate fixed-mode theorem.

Let

[
s(t)=m_{\mathrm{arch}}(t)+C\ge0,
\qquad
w(t)=\sqrt{s(t)}.
]

Then pointwise:

[
w(t)\le s(t)+1
\le |m_{\mathrm{arch}}(t)|+C+1.
]

Consequently, for a literal Fourier mode (F_n),

[
|wF_n|
\le
|m_{\mathrm{arch}}F_n|+(C+1)|F_n|.
]

B3.0B3 supplies the first (L^2) term.  `[ABSTRACT][LEAN]`

B3.0L supplies the unweighted whole-line `Lp` mode and the exact a.e. identification for that literal mode.  `[ABSTRACT][LEAN]`

This proves only:

```text
V_n_m i n ∈ sourceArchimedeanShiftedFormDomain i.
```

It does not prove all vectors of `H_m i` belong to the domain.

### 5.5 Does mode membership immediately give finite-span inclusion?

After Candidate C, yes, structurally.

Since B3.0P is a complex `Submodule`, every finite linear combination of admitted modes is admitted. The exact `E_m_N` or `ccmFiniteSynthesis` inclusion should nevertheless be a separate theorem because it binds the production finite carrier and mode order.

That separate theorem must not be folded into B3.0P’s carrier construction.

### 5.6 Which child first helps density and closedness?

B3.0P is the first necessary **category object**.

B3.0Q, the literal-mode membership theorem, is the first child that materially enables density: once every member of the already-proved complete Hilbert basis is in the Submodule, density becomes an exact closure argument.

Closedness is later. Neither a `Submodule` nor dense basis inclusion proves the multiplication form is closed.

### 5.7 D0.2 equality timing

Equality with D0.2 is necessarily later than:

```text
lawful weighted carrier;
mode/core inclusion;
density;
shifted multiplication form;
closedness/lower-semicontinuity;
bounded W02 and Prime perturbations;
exact finite-core agreement.
```

D0.2 specifies a generally proper dense form domain, a lower-bounded lower-semicontinuous form, and exact finite restrictions. It does not identify that source domain with an arbitrary newly defined weighted carrier.  `[ABSTRACT][PAPER]`

Any candidate that inserts

```text
sourceArchimedeanShiftedFormDomain = Dom(D0.2)
```

as a premise is stopped with:

```text
SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION
```

The associated operator remains a still finer category. D0.3 explicitly separates form-domain membership, operator-domain membership, finite Riesz representation, and operator compression.  `[ABSTRACT][PAPER]`

## 6. Exact scratch candidate

Exact lock:

```text
SHA-256:
  d2fc68954ae6604d1573bbe37b83e08577f60f4d39f5b9b9f3548821ce866a50

bytes:
  2845

wc-lines:
  78

final LF:
  true
```

[Exact B3.0P scratch candidate](sandbox:/mnt/data/GOAL057_B3_0P_SHIFTED_ARCH_FORM_DOMAIN_SUBMODULE_PREFLIGHT_CANDIDATE_2026-08-09.lean)

```lean
import Q3.Proofs.RouteB.D0PstarShiftedArchSqrtWeight
import Q3.Proofs.RouteB.D0PstarSourceLogWindowFourierL2Isometry

noncomputable section

open Complex MeasureTheory
open scoped ENNReal

namespace Q3.RouteB.D0Pstar

private noncomputable def sourceArchimedeanShiftedWeightedImage
    (i : PairIndex) (x : H_m i) : ℝ → ℂ :=
  fun t : ℝ =>
    (sourceArchimedeanShiftedSqrtWeight t : ℂ) *
      ((sourceLogWindowFourierL2Isometry i x :
          MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t

/-- The exact shifted archimedean form domain pulled back to `H_m i` through
B3.0L.  Membership means square-root-weighted whole-line `L²` integrability.
This is not the full-multiplier operator domain and is not identified here with
D0.2's source form domain. -/
noncomputable def sourceArchimedeanShiftedFormDomain
    (i : PairIndex) : Submodule ℂ (H_m i) where
  carrier :=
    {x | MemLp (sourceArchimedeanShiftedWeightedImage i x) 2 volume}
  zero_mem' := by
    have hEq :
        (0 : ℝ → ℂ) =ᵐ[volume]
          sourceArchimedeanShiftedWeightedImage i 0 := by
      filter_upwards
        [MeasureTheory.Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with t ht
      simp [sourceArchimedeanShiftedWeightedImage, ht]
    exact MemLp.ae_eq hEq MemLp.zero
  add_mem' := by
    intro x y hx hy
    have hEq :
        sourceArchimedeanShiftedWeightedImage i x +
            sourceArchimedeanShiftedWeightedImage i y
          =ᵐ[volume]
        sourceArchimedeanShiftedWeightedImage i (x + y) := by
      filter_upwards
        [MeasureTheory.Lp.coeFn_add
          (sourceLogWindowFourierL2Isometry i x)
          (sourceLogWindowFourierL2Isometry i y)] with t ht
      simp only [sourceArchimedeanShiftedWeightedImage, Pi.add_apply,
        map_add, ht]
      ring
    exact MemLp.ae_eq hEq (hx.add hy)
  smul_mem' := by
    intro c x hx
    have hEq :
        c • sourceArchimedeanShiftedWeightedImage i x
          =ᵐ[volume]
        sourceArchimedeanShiftedWeightedImage i (c • x) := by
      filter_upwards
        [MeasureTheory.Lp.coeFn_smul c
          (sourceLogWindowFourierL2Isometry i x)] with t ht
      simp only [sourceArchimedeanShiftedWeightedImage, Pi.smul_apply,
        smul_eq_mul, map_smul, ht]
      ring
    exact MemLp.ae_eq hEq (hx.const_smul c)

@[simp]
theorem mem_sourceArchimedeanShiftedFormDomain_iff
    (i : PairIndex) (x : H_m i) :
    x ∈ sourceArchimedeanShiftedFormDomain i ↔
      MemLp
        (fun t : ℝ =>
          (sourceArchimedeanShiftedSqrtWeight t : ℂ) *
            ((sourceLogWindowFourierL2Isometry i x :
                MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t)
        2 volume := by
  rfl

#print axioms sourceArchimedeanShiftedFormDomain
#print axioms mem_sourceArchimedeanShiftedFormDomain_iff

end Q3.RouteB.D0Pstar
```

The candidate is byte-pinned and statically audited. It has not been run through the project’s pinned Lean toolchain by this judge.

## 7. Mandatory judges

| ID                                         | Mutation or attack                                                                                                      | Required stop                                            |
| ------------------------------------------ | ----------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------- |
| `P057_B3_0P_1_LP_REPRESENTATIVE_AE`        | Define membership using an arbitrary raw representative or replace a.e. transport with pointwise equality               | `B3_0P_LP_QUOTIENT_REPRESENTATIVE_DEPENDENCE`            |
| `P057_B3_0P_2_FORM_OPERATOR_WEIGHT`        | Replace `sourceArchimedeanShiftedSqrtWeight` by the full shifted symbol                                                 | `B3_0P_FORM_OPERATOR_WEIGHT_COLLAPSE`                    |
| `P057_B3_0P_3_ARBITRARY_VECTOR_QUANTIFIER` | Add `∀ x : H_m i, x ∈ domain` from fixed-mode inputs                                                                    | `B3_0P_ARBITRARY_VECTOR_WEIGHTED_DOMAIN_OVERCLAIM`       |
| `P057_B3_0P_4_PREMISE_SURROGATE`           | Assume the target carrier is a Submodule or assume the needed closure statements                                        | `SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION`           |
| `P057_B3_0P_5_FINITE_RIESZ`                | Use `sourceCCMFiniteRieszOperator` to define or certify the ambient form domain                                         | `B3_0P_FINITE_RIESZ_SUBSTITUTED_FOR_AMBIENT_FORM_DOMAIN` |
| `P057_B3_0P_6_EXACT_CARRIER`               | Replace `H_m i` or the B3.0L isometry by an unrelated `Lp` carrier                                                      | `B3_0P_SOURCE_CARRIER_MISMATCH`                          |
| `P057_B3_0P_7_AE_LINEAR_CLOSURE`           | Delete `Lp.coeFn_add/smul` and treat coercion as pointwise definitional                                                 | `B3_0P_LP_LINEAR_CLOSURE_AE_BRIDGE_MISSING`              |
| `P057_B3_0P_8_DEPENDENCY`                  | Add generated PSD, Step33, hbox, payload, PrimeCert, or Aristotle-output support                                        | `ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK`                   |
| `P057_B3_0P_9_SCOPE`                       | Add mode inclusion, density, form, D0.2 equality, graph, operator, compression, numerator, H4a1b, or checkpoint content | `B3_0P_SCOPE_SMUGGLE`                                    |

### Independent controls

1. **Null-set representative control.** Two whole-line functions differing only on a null set must induce the same weighted `MemLp` status. The control must pass through `MemLp.ae_eq`, not pointwise equality.

2. **Form/operator-domain control.** For the diagonal operator (Ae_n=n e_n) on (\ell^2), the square-root-weight form domain and full-weight operator domain differ. A candidate identifying them must fail. `[ABSTRACT][PAPER]`

3. **Basis/all-vector control.** Every basis vector may lie in an unbounded weighted domain while some infinite (\ell^2) combination does not. Fixed-mode membership must not imply `∀ x : H_m i`.

4. **Dependency fingerprints.** The candidate must directly consume B3.0O’s exact square-root weight and B3.0L’s exact whole-line isometry.

## 8. Exact preflight validation

Create only:

```text
q3.lean.aristotle/Goal057B3_0P_ShiftedArchFormDomain_Scratch.lean
```

by byte-for-byte copy of the candidate above.

Before execution:

```bash
test "$(git rev-parse HEAD)" = \
  "ce02a74715282a46ae95ff6fc22de7e578ee7bd1"

test "$(git rev-parse origin/rh_clean)" = \
  "ce02a74715282a46ae95ff6fc22de7e578ee7bd1"

test "$(git diff --cached | sha256sum | cut -d' ' -f1)" = \
  "291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b"
```

Verify:

```text
SHA-256:
  d2fc68954ae6604d1573bbe37b83e08577f60f4d39f5b9b9f3548821ce866a50

bytes:
  2845

wc-lines:
  78

final LF:
  true
```

Run:

```bash
cd q3.lean.aristotle

rg -n \
  'sorry|exact\?|admit|unsafe|native_decide|opaque|axiom |Float' \
  Goal057B3_0P_ShiftedArchFormDomain_Scratch.lean

lake env lean \
  Goal057B3_0P_ShiftedArchFormDomain_Scratch.lean
```

Required preflight result:

```yaml
direct_Lean_exit: 0

imports:
  exact_count: 2
  exact_order:
    - Q3.Proofs.RouteB.D0PstarShiftedArchSqrtWeight
    - Q3.Proofs.RouteB.D0PstarSourceLogWindowFourierL2Isometry

public_surface:
  definitions: 1
  theorems: 1

private_surface:
  definitions: 1
  theorems: 0

forbidden_tokens: 0

axioms:
  every_public_declaration_exactly:
    - propext
    - Classical.choice
    - Quot.sound
```

Run all nine judges in temporary copies. Delete every mutant. Then require:

```text
routeb_status.py --check: PASS
git diff --check: PASS
tracked repository mutation: NONE
route state mutation: NONE
unrelated staged patch SHA: UNCHANGED
exact git status: REPORTED
same living chat: PRESERVED
```

### Binary preflight outcomes

```text
PASS:
  GOAL057_B3_0P_SHIFTED_ARCH_FORM_DOMAIN_SUBMODULE_PREFLIGHT_PROVED
```

Return the exact scratch bytes, direct Lean output, axiom report, dependency fingerprint, and all nine judge fates to this same chat for a separate production-release adjudication.

```text
FAIL_API:
  GOAL057_B3_0P_LP_QUOTIENT_REPRESENTATIVE_API_GAP
```

Use this only if the exact pinned `Lp` coercion/a.e. APIs cannot type the carrier law.

```text
FAIL_CLOSURE:
  GOAL057_B3_0P_MEMLP_SUBMODULE_CLOSURE_API_GAP
```

Use this only if zero/add/smul closure cannot be established without changing the mathematical carrier.

No failure branch authorizes a predicate-only public wrapper, a form, or an operator.

## 9. Exact semantic boundary after preflight success

A successful B3.0P preflight proves only that

[
\boxed{
\left{
x\in H_m(i):
\sqrt{m_{\mathrm{arch}}+C},\Phi_i x\in L^2(\mathbb R)
\right}
}
]

is a complex linear subspace of `H_m i`, where

[
C=|\log\pi|+\log4+6.
]

`[ABSTRACT][LEAN]`

It does not prove:

* any literal mode belongs to the domain;
* `E_m_N` lies in the domain;
* density;
* a shifted multiplication form;
* closedness or lower-semicontinuity;
* equality with D0.2;
* bounded ambient W02 or Prime extensions;
* an associated graph or operator;
* operator-domain membership;
* compression or invariance;
* the continuum numerator;
* H4a1b;
* any coarse checkpoint.

The exact next gap is named:

```text
GOAL057_B3_0Q_LITERAL_MODE_IN_SHIFTED_ARCH_FORM_DOMAIN
```

Its intended theorem shape is:

```lean
theorem V_n_m_mem_sourceArchimedeanShiftedFormDomain
    (i : PairIndex) (n : ℤ) :
    V_n_m i n ∈ sourceArchimedeanShiftedFormDomain i
```

It is not selected or authorized here.

## 10. Strongest attack

> The selected child still only packages a weighted `MemLp` condition. Is this another decorative wrapper?

It is representation progress, not a new analytic estimate. That objection is correct.

It survives because it closes a real category wall that the later proof cannot bypass safely:

```text
raw weighted function predicate
→ quotient-safe complex linear form-domain carrier.
```

Without this object, a later mode/core theorem has nowhere correctly typed to land. More importantly, the selected proof forces every linear operation through the official a.e. laws of `Lp`; it prevents a downstream proof from silently using a representative-dependent pointwise domain.

The standalone predicate A would be decorative. Candidate B is not: its `Submodule` laws are actual proof obligations, and the representative-safety attack is independently observable.

## 11. Meta closeout

**What became smaller?**

The post-B3.0O wall is reduced from a vague “construct a shifted domain” problem to one exact quotient-safe `Submodule` preflight.

**What was killed?**

* a standalone public predicate alias;
* pointwise representative dependence;
* the full shifted symbol as the form-domain weight;
* all-(H_m) membership from fixed-mode facts;
* finite Riesz as an ambient-domain supplier;
* a bundled domain/core/density/form/closedness transaction.

**What must not be tried again?**

Do not define the domain on an arbitrary representative. Do not identify the square-root form domain with the full-multiplier operator domain. Do not call the new carrier D0.2 before an equality theorem.

**Current smallest named gap**

```text
GOAL057_B3_0P_SHIFTED_ARCH_FORM_DOMAIN_SUBMODULE_PREFLIGHT_FAILED
```

until the exact candidate compiles.

**Next cheapest decisive test**

Compile the exact 2,845-byte candidate and run the a.e.-representative and form/operator-category plants.

**Prediction ledger**

```text
Prior post-O candidate:
  the next lawful object is a shifted archimedean form-domain primitive.

Fate:
  CONFIRMED_AND_SHARPENED.
  The exact primitive is a quotient-safe complex Submodule, not a
  standalone predicate and not a form.

Registered prediction:
  the exact 2,845-byte candidate compiles under the pinned toolchain with
  the standard axiom triple.

Status:
  REGISTERED_NOT_YET_TESTED.
```

```yaml
iteration:
  target: GOAL057_B3_0_POST_O_NEXT_NODE_ADJUDICATION
  status: PROGRESS
  failed_strategy: publish_a_predicate_alias_before_proving_the_linear_carrier
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: GOAL057_B3_0P_SHIFTED_ARCH_FORM_DOMAIN_SUBMODULE_PREFLIGHT_FAILED
  invariant_learned: weighted_form_domain_must_be_Lp_quotient_safe_complex_linear_and_use_the_sqrt_shift_not_the_full_symbol
  forbidden_future_move: infer_D0_2_or_operator_domain_semantics_from_the_carrier_definition
  next_decisive_test: exact_B3_0P_untracked_Lean_preflight
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS:
  TRY_GOAL057_B3_0P_SHIFTED_ARCH_FORM_DOMAIN_SUBMODULE_PREFLIGHT

MODE:
  UNTRACKED_EXACT_LEAN_PREFLIGHT
  PRODUCTION_AUTHORIZED: false
  TRACKED_REPOSITORY_MUTATION: false
  ROUTE_STATE_MUTATION: false
  NO_PRODUCTION_AUTHORIZATION_IN_THIS_VERDICT: true

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: ce02a74715282a46ae95ff6fc22de7e578ee7bd1
  require_origin_equal: true

  controlling_request_sha256:
    393c877b44ba5e0e8cc87ad1a86878a8d641313ef4d4d0eabcf309705595e59e
  controlling_request_bytes: 12664
  controlling_request_wc_lines: 343
  controlling_request_final_LF: true

  preserve_staged_patch_sha256:
    291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b

CREATE_UNTRACKED_ONLY:
  - q3.lean.aristotle/Goal057B3_0P_ShiftedArchFormDomain_Scratch.lean

DO_NOT_CREATE:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarShiftedArchFormDomain.lean

EXACT_CANDIDATE:
  source_artifact:
    GOAL057_B3_0P_SHIFTED_ARCH_FORM_DOMAIN_SUBMODULE_PREFLIGHT_CANDIDATE_2026-08-09.lean
  method: BYTE_FOR_BYTE_COPY
  sha256: d2fc68954ae6604d1573bbe37b83e08577f60f4d39f5b9b9f3548821ce866a50
  bytes: 2845
  wc_lines: 78
  final_LF: true
  any_byte_change: STOP_AND_RETURN_CORRECTED_CANDIDATE

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarShiftedArchSqrtWeight
  - Q3.Proofs.RouteB.D0PstarSourceLogWindowFourierL2Isometry

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE_EXACT:
  definitions:
    - sourceArchimedeanShiftedFormDomain
  theorems:
    - mem_sourceArchimedeanShiftedFormDomain_iff
  total: 2

PRIVATE_SURFACE_EXACT:
  definitions:
    - sourceArchimedeanShiftedWeightedImage
  theorems: []
  total: 1

MANDATORY_SEMANTICS:
  - exact_H_m_i_source_carrier
  - exact_B3_0L_whole_line_Lp_isometry
  - exact_B3_0O_square_root_shifted_weight
  - exact_MemLp_2_volume_membership
  - quotient_safety_through_Lp_coeFn_AE_laws
  - complex_Submodule_zero_add_smul_closure
  - no_full_shift_operator_domain
  - no_literal_mode_membership
  - no_finite_span_inclusion
  - no_density
  - no_form_or_closedness
  - no_D0_2_equality
  - no_graph_operator_compression_or_numerator_claim

MANDATORY_JUDGES:
  - P057_B3_0P_1_LP_REPRESENTATIVE_AE
  - P057_B3_0P_2_FORM_OPERATOR_WEIGHT
  - P057_B3_0P_3_ARBITRARY_VECTOR_QUANTIFIER
  - P057_B3_0P_4_PREMISE_SURROGATE
  - P057_B3_0P_5_FINITE_RIESZ
  - P057_B3_0P_6_EXACT_CARRIER
  - P057_B3_0P_7_AE_LINEAR_CLOSURE
  - P057_B3_0P_8_DEPENDENCY
  - P057_B3_0P_9_SCOPE

INDEPENDENT_CONTROLS:
  - null_set_representative_invariance
  - form_domain_not_operator_domain_diagonal_l2_control
  - fixed_basis_membership_not_all_H_m_membership
  - exact_B3_0O_dependency_fingerprint
  - exact_B3_0L_dependency_fingerprint

VALIDATION:
  - verify_HEAD_equals_origin_rh_clean
  - verify_staged_patch_SHA256_unchanged
  - verify_exact_scratch_SHA256_bytes_wc_lines_and_final_LF
  - forbidden_token_scan
  - direct_lake_env_lean_on_scratch
  - exact_two_import_audit
  - exact_public_surface_1_definition_1_theorem
  - exact_private_surface_1_definition_0_theorems
  - print_axioms_for_both_public_declarations
  - require_axioms_exactly_[propext_Classical.choice_Quot.sound]
  - run_all_nine_judges_in_temporary_copies
  - run_all_independent_controls
  - remove_all_mutation_artifacts
  - routeb_status_check
  - git_diff_check
  - exact_git_status_report
  - prove_no_tracked_repository_mutation
  - prove_no_route_state_mutation
  - preserve_same_living_chat

PREFLIGHT_STOP:
  GOAL057_B3_0P_SHIFTED_ARCH_FORM_DOMAIN_SUBMODULE_PREFLIGHT_FAILED

PREFLIGHT_SUCCESS:
  GOAL057_B3_0P_SHIFTED_ARCH_FORM_DOMAIN_SUBMODULE_PREFLIGHT_PROVED

PASS_RETURN:
  - exact_scratch_bytes
  - SHA256_bytes_wc_lines_final_LF
  - direct_Lean_stdout_stderr_and_exit
  - exact_axiom_output
  - exact_import_and_surface_report
  - all_nine_judge_fates
  - independent_control_fates
  - exact_B3_0O_and_B3_0L_dependency_fingerprints
  - same_chat_separate_production_release_request

NEXT_GAP_NOT_AUTHORIZED:
  GOAL057_B3_0Q_LITERAL_MODE_IN_SHIFTED_ARCH_FORM_DOMAIN

NOT_AUTHORIZED:
  - create_the_B3_0P_production_file
  - select_or_authorize_B3_0Q
  - prove_literal_mode_membership_in_this_transaction
  - prove_E_m_N_or_finite_synthesis_inclusion
  - prove_density
  - define_the_shifted_archimedean_form
  - prove_closedness_or_lower_semicontinuity
  - identify_the_carrier_or_form_with_D0_2
  - define_SourceWeilAssociatedGraph
  - define_SourceWeilOperatorDomain
  - define_sourceWeilAssociatedOperator
  - use_the_full_shift_as_the_form_domain_weight
  - infer_all_H_m_weighted_membership_from_modewise_results
  - construct_whole_space_W02_or_Prime_extensions
  - substitute_sourceCCMFiniteRieszOperator_for_an_ambient_operator
  - assert_selected_kTrial_operator_domain_membership
  - assert_compression_or_invariance
  - claim_continuum_numerator
  - invoke_or_close_H4A1B
  - decrement_the_ten_checkpoint_ledger
  - touch_frozen_parent_extract_schedules
  - create_Bus_010
  - release_Goal_055
  - unfreeze_G2_CCM
  - submit_Aristotle
  - promote_Route_B
  - make_PX_or_RH_claim
  - open_fresh_chat

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  active_bus_goal: 057
  bus_010: VOID
  goal_055: HOLD
  g2_ccm: FROZEN
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10
  H4a1b: OPEN
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
```
