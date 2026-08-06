# STATUS: OPEN — UNNORMALIZED FULL-MELLIN/GWIN CROSSWALK SELECTED; RESIDUAL CONTRACT DEFERRED

```yaml
PRIMARY: G6_S2_SELECTED_FULL_MELLIN_GWIN_CROSSWALK_SELECTED
PRIMARY_COUNT: 1

OPERATIVE_CLASS: TRY_G6_S2_D0_SELECTED_FULL_MELLIN_GWIN_CROSSWALK
OPERATIVE_CLASS_COUNT: 1

SELECTED_CANDIDATE: A_REPAIRED
REPAIR:
  - prove_the_unnormalized_full_coordinate_equality
  - include_one_definitionally_algebraic_scaled_corollary
  - do_not_discharge_the_Phase4B_residual_contract

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  PIN: 952d0760a2741ddc2766976295b684cddb26baa4
  ORIGIN_HEAD_EQUALS_PIN: true
  PIN_CORRECTION_ACCEPTED: true
  SOURCE_LOCK_MISMATCH: false
  PIN_COMMIT: "[MacOS][rh_clean][Docs] Research Goal 056 full Mellin Gwin crosswalk"

SUPPLIER_SHA256:
  D0KTrialStage2: aabaf47cb484f0157fd7b2ac4f30811aec9595116c1193715e41de8b520393cd
  D0PstarMuntzCenteredCoordinateLock: ce0226f7bd028449a04cae0dfa28e8998a0e835eba5ec0a56a93f0ae18b073a5
  D0PstarMuntzGalerkinResidualContract: 1f9b0f16210271fc699107f991a244421d98bbdafd695d5a585dae4aca4f73ff
  D0PstarProjectedMellinCoordinate: 8f0c764615873a6a3e677d13d86ba6686cc5f4b31354749e4cf171f36fed139e
  WindowEndpointBridge: e3a021173e66f61389ac218ceaf6c898d64bb9854babea50f435b131ae21c44a
  D0LogWindowMeasureTransport: 59c6d9a3a3a3c77427997665216e3ff797b9e2dc925cb63e5e9e6df0df64905b
  MuntzV3Core: 7df74238ff1462eb750b0f975f4b87f4b9eec5f1f46c104890d1345b8e2cf1ca
  STATUS: ACCEPTED_FROM_CORRECTED_DISK_RECHECK_WITH_CONNECTOR_CONTENT_CROSSCHECK

ARSENAL:
  MANDATE_ACCEPTED: true
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

TRANSACTION:
  NAME: G6_S2_D0_SELECTED_FULL_MELLIN_GWIN_CROSSWALK
  OWNED_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarFullMellinGwinCrosswalk.lean
  SOLE_PROJECT_IMPORT: Q3.Proofs.RouteB.D0PstarProjectedMellinCoordinate
  NAMESPACE: Q3.RouteB.D0Pstar

PUBLIC_SURFACE:
  DEFINITIONS: 1
  THEOREMS: 2
  PRIVATE_PRODUCTION_DECLARATIONS: 0
  LOCAL_HAVE_HELPERS: permitted

PUBLIC_DEFINITION:
  - selectedFullMellinCoordinate

PUBLIC_THEOREMS:
  - selectedFullMellinCoordinate_eq_selectedGwinTransformCoordinate
  - selectedTrialNormalizer_mul_selectedFullMellinCoordinate_eq_selectedScaledGwinTransformCoordinate

PHASE4B_CONTRACT_DISCHARGED: false
COMPACT_OPEN_DECAY_PROVED: false
SLOT_S2_PROVED: false

STOP: G6_S2_SELECTED_FULL_MELLIN_GWIN_CROSSWALK_MISSING
SUCCESS: G6_S2_SELECTED_FULL_MELLIN_AND_SCALED_GWIN_CROSSWALK_PROVED

SOLE_NEXT_NODE_NOT_AUTHORIZED:
  G6_S2_D0_RESIDUAL_MELLIN_LINEARITY_AND_CONTRACT_DISCHARGE
NEXT_JUMP_TARGET:
  selectedGalerkinResidualMellinCoordinate_eq_projected_sub_scaledFull

PHASE_KEY_CHANGE: false
NEW_CHAT: false
ARISTOTLE_SUBMISSION: NONE

PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

## 1. Corrected source lock

The corrected full pin is exact: `origin/rh_clean` resolves to `952d0760a2741ddc2766976295b684cddb26baa4`, and its commit message is the stated Goal-056 full-Mellin/Gwin research entry. No source-lock failure is emitted for the superseded transcription suffix.   `[ABSTRACT][PAPER]`

The active control delegates this decision to Codex and Proshka, keeps PX/RH as the sole owner gate, and requires continuation of the existing chat while the phase key is unchanged.  `[ABSTRACT][PAPER]`

The supplier SHA-256 values in the header are accepted from the corrected live-disk recheck. The connector independently confirms the corresponding definitions and theorem surfaces at the corrected pin; it does not itself expose a byte-level SHA-256 operation.

The Arsenal mandate is accepted. C04 controls the `dStar`/Lebesgue and `E_star`/`Estar` category changes; C09 fixes the full-coordinate object before proof search; C10 forbids defining the new scalar from `Gwin` and then claiming an object-first bridge.   `[ABSTRACT][PAPER]`

## 2. Closed inputs

Phase 4E has proved the object-first coordinate of the normalized **projected** trial:

```lean
selectedProjectedMellinCoordinate S k z
  =
selectedRawTransformCoordinate S k z
```

using the literal `kTrial_m_N`, the source `dStar` measure, the exact positive window, and the reflected `rawFplus ... (-z)` convention. It did not prove a full-object/Gwin theorem or the Phase-4B contract.   `[COFINAL_FAMILY][LEAN]`

The full D0 object is independently source-locked:

```lean
gTrial_m i h hLp = hLp.toLp (E_star h)
```

where

```lean
E_star h u =
  sqrt(u) * ∑' n : ℕ+, h (n*u).
```

Thus the full coordinate must be built from `gTrial_m`, not from the finite projection and not from `Gwin`.  `[ABSTRACT][LEAN]`

The Müntz object is:

```lean
Gwin h Λ s =
  ∫ u in Ioo Λ⁻¹ Λ,
    Estar h u * (u : ℂ) ^ (s - 1)
```

and the selected production convention already fixes `s = -I*z`.   `[ABSTRACT][LEAN]`

## 3. Candidate decision

| Candidate                                                 | Verdict                                     | Reason                                                                                                                             |
| --------------------------------------------------------- | ------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------- |
| **A — full coordinate only**                              | **Selected with one-line scaled corollary** | One source object, one measure conversion, one exponent identity, one endpoint conversion                                          |
| **B — full coordinate plus immediate contract discharge** | Deferred                                    | Contract discharge is not merely `ring`; it needs a separate linearity theorem for the Mellin integral on literal `Lp` differences |
| Kill full route                                           | Rejected                                    | No sign, type, source, or normalization contradiction exists                                                                       |

The selected operative class is:

```text
TRY_G6_S2_D0_SELECTED_FULL_MELLIN_GWIN_CROSSWALK
```

### Why Candidate B is not authorized

Phase 4B defines the literal residual as

```lean
selectedTrialNormalizer •
  (projected gTrial_m_N - full gTrial_m)
```

and separately defines the integral of that residual. Its contract remains a `Prop`, not a theorem or axiom.  `[COFINAL_FAMILY][LEAN]`

To derive the contract after the two coordinate equalities, Lean still needs:

[
\int a,(f-g),K
==============

\int afK-\int agK.
]

That is not automatically available from scalar equalities. Bochner integration uses a zero value for non-integrable functions, and general subtraction linearity needs integrability evidence or a separately constructed continuous linear functional. Phase 4C intentionally used an unrestricted transport theorem that remains valid under the non-integrable convention; therefore that theorem does **not** silently supply the missing linearity hypotheses.   `[ABSTRACT][LEAN]`

Adding an `Lp → L¹` bounded-kernel theorem is mathematically reasonable, but it is a separate proof edge. Candidate B would conceal it under the word “algebraic.”

This is not a kill of the contract route. It is a minimal-lemma split.

## 4. Exact selected object

```lean
/--
The multiplicative Mellin coordinate of the literal unnormalized full
D0 trial on the selected source window.
-/
noncomputable def selectedFullMellinCoordinate
    (S : ProlateCanonicalSourceData)
    (k : ℕ) (z : ℂ) : ℂ :=
  let i := selectedPairIndex S k
  let h := selectedProlateTrial S k
  let hLp := S.source.eStar_memLp i
  ∫ u : ℝ,
      (gTrial_m i h hLp : H_m i) u *
        (u : ℂ) ^ (-Complex.I * z)
    ∂(dStar.restrict (I_m i))
```

`[COFINAL_FAMILY][CONDITIONAL]`

This definition contains:

* the unprojected `gTrial_m`;
* the stored `MemLp` witness;
* the literal selected parent/extract index;
* `dStar.restrict (I_m i)`;
* the exact kernel (u^{-iz}).

It contains no `Gwin`, `rawFplus`, coefficient row, scalar defect, or fitted normalizer.

## 5. Exact public theorems

### Base equality

```lean
theorem selectedFullMellinCoordinate_eq_selectedGwinTransformCoordinate
    (S : ProlateCanonicalSourceData)
    (k : ℕ) (z : ℂ) :
    selectedFullMellinCoordinate S k z =
      selectedGwinTransformCoordinate S k z := by
  ...
```

`[COFINAL_FAMILY][CONDITIONAL]`

Expanded, the theorem says:

[
\int_{[\Lambda^{-1},\Lambda]}
gTrial_m(u),u^{-iz},\frac{du}{u}
================================

\int_{(\Lambda^{-1},\Lambda)}
Estar(h,u),u^{-iz-1},du,
]

where

[
\Lambda=\lambda_m(\operatorname{selectedPairIndex}(S,k)).
]

### One-line scaled corollary

```lean
theorem
    selectedTrialNormalizer_mul_selectedFullMellinCoordinate_eq_selectedScaledGwinTransformCoordinate
    (S : ProlateCanonicalSourceData)
    (k : ℕ) (z : ℂ) :
    (selectedTrialNormalizer S k : ℂ) *
        selectedFullMellinCoordinate S k z =
      selectedScaledGwinTransformCoordinate S k z := by
  rw [selectedFullMellinCoordinate_eq_selectedGwinTransformCoordinate]
  rfl
```

`[COFINAL_FAMILY][CONDITIONAL]`

This corollary is included because omitting it would manufacture a one-line future boundary. It introduces no new integral, object, hypothesis, or normalization choice.

It does **not** distribute the normalizer across a residual difference.

## 6. Exact source convention

Let

```text
i = selectedPairIndex S k
h = selectedProlateTrial S k
Λ = lambda_m i.
```

The D0 coordinate is:

[
\int_{Icc(\Lambda^{-1},\Lambda)}
E_\star(h,u),u^{-iz},d^\star u.
]

The source measure is:

[
d^\star u
=========

u^{-1},du
]

on this positive window. The production definition is literally a Lebesgue measure with density `ENNReal.ofReal u⁻¹`.  `[ABSTRACT][LEAN]`

After expanding the density:

[
E_\star(h,u),u^{-iz},u^{-1}.
]

On (u>0),

[
u^{-iz},u^{-1}
==============

u^{(-iz)-1}.
]

Thus:

[
E_\star(h,u),u^{-iz},u^{-1}
===========================

Estar(h,u),u^{(-iz)-1}.
]

The Müntz argument is therefore exactly:

[
s=-iz,
]

not (z), (iz), or (-z).

The two endpoint values contribute nothing because the converted measure is atomless Lebesgue volume. The existing project wrapper records this `Icc = Ioo` law.  `[ABSTRACT][LEAN]`

### Endpoint-wrapper repair

The public project wrapper takes an unnecessary global `LocallyIntegrable` premise even though its body invokes the unconditional atomless endpoint theorem. The current source data supplies an `Lp` certificate on the selected window, not global local integrability of the Müntz integrand.

Therefore the selected proof should invoke:

```lean
MeasureTheory.integral_Icc_eq_integral_Ioo
```

directly after converting to Lebesgue volume.

It must not introduce a new global `LocallyIntegrable` hypothesis merely to fit the stronger wrapper type.

## 7. Exact proof route

1. Set `i`, `h`, and the stored `hLp`.

2. Obtain the representative equality:

   ```lean
   (gTrial_m i h hLp : ℝ → ℂ)
     =ᵐ[dStar.restrict (I_m i)]
   E_star h
   ```

   using `MemLp.coeFn_toLp`.

3. Rewrite the coordinate integral by `integral_congr_ae`. Do not assert pointwise equality of the `Lp` representative.

4. Expand:

   ```lean
   dStar = volume.withDensity (fun u => ENNReal.ofReal u⁻¹)
   ```

   using the same pinned API already exercised in Phase 4C:

   ```lean
   setIntegral_withDensity_eq_setIntegral_toReal_smul
   ```

   Mathlib is pinned to v4.26.0 at revision `2df2f015...`.  `[ABSTRACT][LEAN]`

5. For `u ∈ I_m i`, prove `0 < u` from `1 < lambda_m i`.

6. Prove the literal source identity:

   ```lean
   E_star h u =
     EStarMuntzZeroMassContinuation.Estar h u
   ```

   by unfolding only the two starred-sum definitions and normalizing the `PNat` coercion.

7. Under `0 < u`, prove:

   ```lean
   (u⁻¹ : ℂ) *
       (u : ℂ) ^ (-Complex.I * z)
     =
   (u : ℂ) ^ ((-Complex.I * z) - 1)
   ```

   using `Complex.cpow_sub`, `Complex.cpow_one`, and the nonzero fact derived from positivity.

8. Use `setIntegral_congr_fun` on `I_m i`.

9. Unfold `I_m` and replace `Icc Λ⁻¹ Λ` with `Ioo Λ⁻¹ Λ` through the unconditional atomless endpoint theorem.

10. Fold `EStarMuntzZeroMassContinuation.Gwin`, then unfold `selectedGwinTransformCoordinate`.

11. Prove the scaled corollary by one rewrite and `rfl`.

No Fourier reconstruction, coefficient sum, logarithmic transport, or Phase-4B hypothesis is involved.

## 8. K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  object:
    gTrial_m
  object_status:
    full_unnormalized_unprojected

  selected_index:
    selectedPairIndex S k
  index_expansion:
    "(S.canonical.parent (S.canonical.extract k)).1"

  source_trial:
    selectedProlateTrial S k
  representative:
    E_star selectedProlateTrial
  representative_relation:
    almost_everywhere_only

  d0_measure:
    dStar.restrict (I_m i)
  density_after_expansion:
    u_inverse_against_volume

  d0_kernel:
    "(u : ℂ) ^ (-Complex.I * z)"

  muntz_source:
    EStarMuntzZeroMassContinuation.Estar
  muntz_argument:
    "-Complex.I * z"
  muntz_kernel:
    "(u : ℂ) ^ ((-Complex.I * z) - 1)"

  d0_window:
    "Icc (lambda_m i)⁻¹ (lambda_m i)"
  muntz_window:
    "Ioo (lambda_m i)⁻¹ (lambda_m i)"
  endpoint_law:
    atomless_volume_only

  base_normalization:
    none
  scaled_corollary_orientation:
    selectedTrialNormalizer_mul_coordinate

  forbidden_object_aliases:
    - gTrial_m_N
    - kTrial_m_N
    - rawFplus
    - selectedGalerkinCoordinateDefect
    - Gwin_defined_coordinate
```

`[COFINAL_FAMILY][CONDITIONAL]`

## 9. Mandatory semantic plants

### P056O-1 — full versus projected object

Mutation:

```text
gTrial_m
→ gTrial_m_N
```

or:

```text
gTrial_m
→ kTrial_m_N.
```

Expected:

```text
G6_S2_FULL_MELLIN_PROJECTED_OBJECT_SUBSTITUTION
```

Phase 4E already shows that the projected normalized object produces `rawFplus`, not the full `Gwin` coordinate.

### P056O-2 — `Lp` representative seam

Mutation:

```text
a.e. equality from MemLp.coeFn_toLp
→ asserted pointwise equality for every u.
```

Expected:

```text
G6_S2_FULL_MELLIN_LP_POINTWISE_SURROGATE
```

No theorem may collapse an `Lp` quotient representative to a global pointwise identity.

### P056O-3 — density

Mutation:

```text
dStar.restrict (I_m i)
→ volume.restrict (I_m i)
```

while retaining the same target.

Expected:

```text
G6_S2_FULL_MELLIN_DSTAR_DENSITY_MISMATCH
```

The missing factor (u^{-1}) changes the exponent from ((-iz)-1) to (-iz).

### P056O-4 — endpoint law

Mutation:

```text
replace atomless volume by a measure with an atom at Λ⁻¹ or Λ
```

in the endpoint test fixture.

Expected:

```text
G6_S2_FULL_MELLIN_ENDPOINT_ATOM_MISMATCH
```

This proves that `Icc = Ioo` is justified by atomlessness, not by an unproved endpoint vanishing statement.

### P056O-5 — exponent and positivity

Mutations:

```text
(-I*z)-1 → (-I*z)+1
```

or:

```text
drop the positivity proof before rewriting complex cpow.
```

Expected:

```text
G6_S2_FULL_MELLIN_CPOW_EXPONENT_OR_BRANCH_MISMATCH
```

### P056O-6 — same starred source

Mutation:

```text
Estar h u
→ h u
```

or omit the factor `sqrt u` or the `PNat` sum.

Expected:

```text
G6_S2_FULL_MELLIN_ESTAR_SOURCE_MISMATCH
```

### P056O-7 — scaled versus unscaled coordinate

Mutation:

```text
selectedFullMellinCoordinate
=
selectedScaledGwinTransformCoordinate
```

without the left normalizer.

Expected:

```text
G6_S2_FULL_MELLIN_SCALE_LEVEL_MISMATCH
```

These seven plants test different facts: object level, quotient semantics, measure, endpoints, complex-power branch, source identity, and normalization level.

## 10. Validation boundary

Required:

```text
SOURCE
- exact HEAD/origin equality
- all seven supplied SHA-256 values rechecked before edit

LEAN
- direct Lean on D0PstarFullMellinGwinCrosswalk.lean
- dedicated target build
- full build
- q3_check PASS

TAINT
- no sorry
- no admit
- no exact?
- no native_decide
- no declared axiom
- no opaque proof certificate
- no Float
- no import from aristotle_output
- no import from ACTIVE/RequestProject

SURFACE
- exactly one public definition
- exactly two public theorems
- zero private production declarations

PLANTS
- P056O-1 through P056O-7 all fire
- all temporary mutation files removed

AXIOMS
- #print axioms selectedFullMellinCoordinate_eq_selectedGwinTransformCoordinate
- #print axioms selectedTrialNormalizer_mul_selectedFullMellinCoordinate_eq_selectedScaledGwinTransformCoordinate
- exact expected set:
  [propext, Classical.choice, Quot.sound]

INFRASTRUCTURE
- proof DB import: all three declarations indexed; both theorems proven
- all 67 orchestration tests PASS
- strict Spine PASS
- knowledge.db integrity = ok
- aristotle_proofs.db integrity = ok
- observability.db integrity = ok
- observability source/stale counts reported
- git diff --check
- exact git status
```

Aristotle is **forbidden**. This is local measure, `Lp`, endpoint, and complex-power algebra.

## 11. Sole next node after success

Not authorized in this batch:

```text
G6_S2_D0_RESIDUAL_MELLIN_LINEARITY_AND_CONTRACT_DISCHARGE
```

Its exact jump target is:

```lean
theorem
    selectedGalerkinResidualMellinCoordinate_eq_projected_sub_scaledFull
    (S : ProlateCanonicalSourceData)
    (k : ℕ) (z : ℂ) :
    selectedGalerkinResidualMellinCoordinate S k z =
      selectedProjectedMellinCoordinate S k z -
        (selectedTrialNormalizer S k : ℂ) *
          selectedFullMellinCoordinate S k z
```

That next transaction must prove the required bounded-kernel `Lp → L¹` integrability or construct the exact continuous linear Mellin functional. Only then may it discharge:

```lean
D0PstarMuntzGalerkinResidualCrosswalkContract S.
```

Compact-open decay remains a separate later wall even after the contract is proved.

## 12. Strongest attack

> The proof may appear to derive the correct exponent by formal simplification while silently using the wrong branch of complex power.

This is the main risk.

The identity

[
u^{-iz}u^{-1}=u^{-iz-1}
]

is legal here only because the selected window lies strictly in (u>0). A global rewrite on arbitrary real (u), or a rewrite based merely on syntactic nonzeroness without reconciling the positive-real logarithm, is not accepted.

The second attack is:

> Why not discharge the residual contract immediately after obtaining the two scalar coordinate equalities?

Because equality of the two endpoint scalar values does not establish linearity of the integral on the literal `Lp` difference. Doing so without integrability would use a functional law that has not been proved. Defining the residual coordinate as the scalar difference instead would be a C10 surrogate.

## 13. Final proposal

Prove the unnormalized full-coordinate theorem and its one-line scaled corollary. Do not bundle the residual contract.

Registered prediction:

```text
P056O-A:
  the base theorem closes in one file from coeFn_toLp,
  withDensity conversion, positive-window cpow algebra, and endpoint removal.

P056O-B:
  the principal Lean friction will be PNat coercion in E_star = Estar
  and real-scalar orientation after withDensity expansion.

P056O-C:
  the later residual contract will require a genuine bounded-kernel
  integrability/linearity lemma; it will not close by ring normalization alone.
```

### Meta closeout

**What became smaller?**

```text
full object to Gwin plus residual contract
```

has become:

```text
full object to Gwin now
→ residual-coordinate linearity next
→ compact-open decay later.
```

**What was killed?**

* defining the full coordinate from `Gwin`;
* replacing the full object by the finite projection;
* inserting the normalizer into the base object;
* global pointwise use of an `Lp` representative;
* treating Candidate B as pure algebra;
* introducing global local-integrability merely to use a stronger endpoint wrapper.

**Current smallest named gap:**

```text
G6_S2_SELECTED_FULL_MELLIN_GWIN_CROSSWALK_MISSING
```

**Fate of prior predictions:**

```text
Phase-4E prediction that the full E_star/Gwin coordinate is next:
  CONFIRMED.

Prediction that compact-open decay remains independent:
  CONFIRMED.

Candidate-B hypothesis that contract discharge may be immediate algebra:
  REFUTED BY THE INTEGRAL-LINEARITY AUDIT.
```

```yaml
iteration:
  target: selected_full_Mellin_to_Gwin
  status: OPEN
  failed_strategy: bundle_coordinate_of_difference_with_two_scalar_coordinate_equalities
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: G6_S2_SELECTED_FULL_MELLIN_GWIN_CROSSWALK_MISSING
  invariant_learned: the full unprojected object, du_over_u density, positive cpow branch, and open-window Gwin exponent must remain literal
  forbidden_future_move: define_an_object_coordinate_from_the_desired_scalar_Gwin_or_use_integral_linearity_without_integrability
  next_decisive_test: direct_Lean_compile_of_the_unnormalized_full_coordinate_theorem_with_all_seven_plants
  progress_class: PROOF_PROGRESS
  route_score: 5
```

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS:
  TRY_G6_S2_D0_SELECTED_FULL_MELLIN_GWIN_CROSSWALK

TRANSACTION:
  G6_S2_D0_SELECTED_FULL_MELLIN_GWIN_CROSSWALK

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

PHASE:
  phase_key_change: false
  reuse_existing_chat: true
  fresh_chat: forbidden

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: 952d0760a2741ddc2766976295b684cddb26baa4

  required_sha256:
    q3.lean.aristotle/Q3/Proofs/RouteB/D0KTrialStage2.lean:
      aabaf47cb484f0157fd7b2ac4f30811aec9595116c1193715e41de8b520393cd
    q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzCenteredCoordinateLock.lean:
      ce0226f7bd028449a04cae0dfa28e8998a0e835eba5ec0a56a93f0ae18b073a5
    q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzGalerkinResidualContract.lean:
      1f9b0f16210271fc699107f991a244421d98bbdafd695d5a585dae4aca4f73ff
    q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarProjectedMellinCoordinate.lean:
      8f0c764615873a6a3e677d13d86ba6686cc5f4b31354749e4cf171f36fed139e
    q3.lean.aristotle/Q3/Proofs/RouteB/WindowEndpointBridge.lean:
      e3a021173e66f61389ac218ceaf6c898d64bb9854babea50f435b131ae21c44a
    q3.lean.aristotle/Q3/Proofs/RouteB/D0LogWindowMeasureTransport.lean:
      59c6d9a3a3a3c77427997665216e3ff797b9e2dc925cb63e5e9e6df0df64905b
    q3.lean.aristotle/Q3/Proofs/RouteB/MuntzV3/Core.lean:
      7df74238ff1462eb750b0f975f4b87f4b9eec5f1f46c104890d1345b8e2cf1ca

ON_SOURCE_MISMATCH:
  stop: G6_S2_FULL_MELLIN_SOURCE_LOCK_MISMATCH
  edit_files: false

CREATE:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarFullMellinGwinCrosswalk.lean

SOLE_PROJECT_IMPORT:
  Q3.Proofs.RouteB.D0PstarProjectedMellinCoordinate

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE:
  definitions: 1
  theorems: 2
  private_production_declarations: 0

PUBLIC_DEFINITION: |
  noncomputable def selectedFullMellinCoordinate
      (S : ProlateCanonicalSourceData)
      (k : ℕ) (z : ℂ) : ℂ :=
    let i := selectedPairIndex S k
    let h := selectedProlateTrial S k
    let hLp := S.source.eStar_memLp i
    ∫ u : ℝ,
        (gTrial_m i h hLp : H_m i) u *
          (u : ℂ) ^ (-Complex.I * z)
      ∂(dStar.restrict (I_m i))

PUBLIC_THEOREM_1: |
  theorem selectedFullMellinCoordinate_eq_selectedGwinTransformCoordinate
      (S : ProlateCanonicalSourceData)
      (k : ℕ) (z : ℂ) :
      selectedFullMellinCoordinate S k z =
        selectedGwinTransformCoordinate S k z := by
    ...

PUBLIC_THEOREM_2: |
  theorem
      selectedTrialNormalizer_mul_selectedFullMellinCoordinate_eq_selectedScaledGwinTransformCoordinate
      (S : ProlateCanonicalSourceData)
      (k : ℕ) (z : ℂ) :
      (selectedTrialNormalizer S k : ℂ) *
          selectedFullMellinCoordinate S k z =
        selectedScaledGwinTransformCoordinate S k z := by
    rw [selectedFullMellinCoordinate_eq_selectedGwinTransformCoordinate]
    rfl

REQUIRED_PROOF_ROUTE:
  - obtain the gTrial_m representative only almost everywhere via MemLp.coeFn_toLp
  - rewrite the coordinate integral by integral_congr_ae
  - expand dStar with setIntegral_withDensity_eq_setIntegral_toReal_smul
  - derive u_positive from membership in the exact I_m window
  - unfold and prove exact E_star_equals_Muntz_Estar
  - prove u_inverse_times_u_cpow_minus_I_z equals u_cpow_minus_I_z_minus_one
  - use Complex.cpow_sub and Complex.cpow_one only under positivity
  - use setIntegral_congr_fun on I_m
  - use MeasureTheory.integral_Icc_eq_integral_Ioo directly
  - fold Gwin at argument minus_I_times_z
  - fold selectedGwinTransformCoordinate
  - prove the scaled corollary by rewrite and rfl

FORBIDDEN_PROOF_ROUTE:
  - define selectedFullMellinCoordinate from Gwin
  - replace gTrial_m by gTrial_m_N
  - replace gTrial_m by kTrial_m_N
  - assert pointwise equality of the Lp representative
  - replace dStar by volume without its density
  - rewrite complex cpow outside the positive window
  - add a global LocallyIntegrable hypothesis to use WindowEndpointBridge
  - prove or assume the Phase4B contract
  - define the residual coordinate as a scalar difference

K6_OBJECT_PRECOMMIT:
  object: gTrial_m_full_unnormalized
  index: selectedPairIndex_S_k
  source_trial: selectedProlateTrial_S_k
  representative_relation: almost_everywhere
  d0_measure: dStar_restrict_I_m
  density: u_inverse
  d0_kernel: u_cpow_minus_I_z
  muntz_source: Estar_same_starred_sum
  muntz_argument: minus_I_times_z
  muntz_exponent: minus_I_z_minus_one
  d0_window: Icc_lambda_inverse_lambda
  muntz_window: Ioo_lambda_inverse_lambda
  endpoints: removed_by_atomless_volume
  base_normalization: none
  scaled_orientation: normalizer_times_coordinate

MANDATORY_PLANTS:
  P056O_1_FULL_NOT_PROJECTED:
    mutation: replace_gTrial_m_by_gTrial_m_N_or_kTrial_m_N
    expected: G6_S2_FULL_MELLIN_PROJECTED_OBJECT_SUBSTITUTION

  P056O_2_LP_REPRESENTATIVE:
    mutation: replace_ae_representative_by_global_pointwise_equality
    expected: G6_S2_FULL_MELLIN_LP_POINTWISE_SURROGATE

  P056O_3_DSTAR_DENSITY:
    mutation: replace_dStar_by_volume_without_u_inverse
    expected: G6_S2_FULL_MELLIN_DSTAR_DENSITY_MISMATCH

  P056O_4_ENDPOINT_ATOM:
    mutation: endpoint_fixture_measure_contains_dirac_atom
    expected: G6_S2_FULL_MELLIN_ENDPOINT_ATOM_MISMATCH

  P056O_5_CPOW_EXPONENT:
    mutations:
      - replace_minus_I_z_minus_one_by_minus_I_z_plus_one
      - remove_positive_window_guard
    expected: G6_S2_FULL_MELLIN_CPOW_EXPONENT_OR_BRANCH_MISMATCH

  P056O_6_ESTAR_SOURCE:
    mutations:
      - omit_sqrt_u
      - replace_Estar_by_unstarred_h
    expected: G6_S2_FULL_MELLIN_ESTAR_SOURCE_MISMATCH

  P056O_7_SCALE_LEVEL:
    mutation: equate_unnormalized_full_coordinate_to_scaled_Gwin
    expected: G6_S2_FULL_MELLIN_SCALE_LEVEL_MISMATCH

VALIDATION:
  - verify HEAD equals origin before editing
  - verify all seven SHA-256 locks
  - lake env lean q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarFullMellinGwinCrosswalk.lean
  - dedicated target build
  - full build
  - bash scripts/q3_check.sh q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarFullMellinGwinCrosswalk.lean
  - scan for sorry admit exact? native_decide axiom opaque Float
  - scan for imports from aristotle_output or ACTIVE RequestProject
  - require exactly one public definition
  - require exactly two public theorems
  - require zero private production declarations
  - fire P056O_1 through P056O_7
  - remove all temporary mutation files
  - print axioms for both public theorems
  - require exactly [propext, Classical.choice, Quot.sound]
  - proof database reimport
  - require all three declarations indexed and both theorems proven
  - run all 67 orchestration tests
  - python3 orchestrator/spine.py --strict --reason goal-close
  - require strict Spine PASS
  - run SQLite integrity_check on knowledge.db
  - run SQLite integrity_check on aristotle_proofs.db
  - run SQLite integrity_check on observability.db
  - require all three results equal ok
  - report observability source and stale counts
  - git diff --check
  - exact git status report

STOP:
  G6_S2_SELECTED_FULL_MELLIN_GWIN_CROSSWALK_MISSING

SUCCESS:
  G6_S2_SELECTED_FULL_MELLIN_AND_SCALED_GWIN_CROSSWALK_PROVED

FAILURE_CODES:
  - G6_S2_FULL_MELLIN_SOURCE_LOCK_MISMATCH
  - G6_S2_FULL_MELLIN_PROJECTED_OBJECT_SUBSTITUTION
  - G6_S2_FULL_MELLIN_LP_POINTWISE_SURROGATE
  - G6_S2_FULL_MELLIN_DSTAR_DENSITY_MISMATCH
  - G6_S2_FULL_MELLIN_ENDPOINT_ATOM_MISMATCH
  - G6_S2_FULL_MELLIN_CPOW_EXPONENT_OR_BRANCH_MISMATCH
  - G6_S2_FULL_MELLIN_ESTAR_SOURCE_MISMATCH
  - G6_S2_FULL_MELLIN_SCALE_LEVEL_MISMATCH
  - G6_S2_FULL_MELLIN_ENDPOINT_BRIDGE_OVERSTRENGTHENED
  - G6_S2_FULL_MELLIN_PLANT_INERT
  - LEAN_BUILD_FAIL

SOLE_NEXT_NODE_NOT_AUTHORIZED:
  name: G6_S2_D0_RESIDUAL_MELLIN_LINEARITY_AND_CONTRACT_DISCHARGE
  jump_target: |
    theorem
        selectedGalerkinResidualMellinCoordinate_eq_projected_sub_scaledFull
        (S : ProlateCanonicalSourceData)
        (k : ℕ) (z : ℂ) :
        selectedGalerkinResidualMellinCoordinate S k z =
          selectedProjectedMellinCoordinate S k z -
            (selectedTrialNormalizer S k : ℂ) *
              selectedFullMellinCoordinate S k z

FORBIDDEN:
  - modify Phase4A Phase4B Phase4C Phase4D or Phase4E production files
  - discharge the Phase4B contract
  - prove raw_Gwin_equality beyond the selected full coordinate
  - prove residual decay
  - prove compact_open_convergence
  - prove strict_SlotS2
  - edit Q3.Main
  - edit Goal_055
  - create Bus_010
  - submit Aristotle
  - promote Route_B
  - make PX_or_RH_claim
  - open a fresh Proshka chat

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  bus_010: VOID
  goal_055: HOLD
  Aristotle_submission: NONE
  route_promotion: false
  PX_RH_CLAIM: NOT_MADE
```
