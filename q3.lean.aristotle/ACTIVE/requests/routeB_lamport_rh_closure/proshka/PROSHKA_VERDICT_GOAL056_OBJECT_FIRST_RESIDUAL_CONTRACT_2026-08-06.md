# STATUS: CONDITIONAL — NAMED OBJECT-FIRST RESIDUAL CROSSWALK CONTRACT SELECTED

```yaml
PRIMARY: G6_S2_NAMED_OBJECT_FIRST_RESIDUAL_CONTRACT_SELECTED
OPERATIVE_CLASS: TRY_NAMED_RESIDUAL_CROSSWALK_CONTRACT
OPERATIVE_CLASS_COUNT: 1
SELECTED_PATH: B

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  PIN: 8487d4dc3557b8bfe4d57f61c3b67508d7d19f23
  ORIGIN_HEAD_EQUALS_PIN: true
  PIN_COMMIT: "[MacOS][rh_clean][RouteB] Record Goal 056 residual research fork"

CONTROL:
  CODEX_CONTROL_STATUS: ACTIVE
  CODEX_CONTROL_SHA256: fc77ff8d7483c87744f07e8aea3d59b08f9b5340541d3bf414885f239dfafc4e
  AUTHORITY: CODEX_PLUS_PROSHKA
  SOLE_OWNER_GATE: PX_RH_CLAIM
  OWNER_DEFERRAL_ALLOWED_HERE: false

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
  ANSWER_SHA256: 322deb89933e6fac467714377dda92434f1ddddba8b1c80aaf8d2f127963d005
  RESULT: G6_S2_XW6_SAME_INDEX_COORDINATE_CONTRACT_MATERIALIZED_RESIDUAL_OPEN
  CURRENT_PIN_MUTATION_AFTER_PHASE4A: INSIGHTS_ONLY
  SOURCE_FAMILY_LOCK: PASS
  PARENT_EXTRACT_LOCK: PASS
  CENTERED_ORIENTATION_LOCK: PASS
  OBJECT_FIRST_RESIDUAL_IDENTIFICATION: OPEN
  COMPACT_OPEN_RESIDUAL_DECAY: OPEN

SELECTED_TRANSACTION:
  NAME: G6_S2_D0PSTAR_MUNTZ_NAMED_RESIDUAL_CROSSWALK_CONTRACT
  KIND: CONDITIONAL_INTERFACE_PLUS_HOLE_FREE_RECEIVER
  OWNED_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzGalerkinResidualContract.lean
  SOLE_IMPORT: Q3.Proofs.RouteB.D0PstarMuntzCenteredCoordinateLock
  NAMESPACE: Q3.RouteB.D0Pstar
  CONTRACT_PROOF_CLAIMED: false
  CONTRACT_DECLARED_AS_AXIOM: false
  SLOT_S2_CLOSED: false
  DECAY_BUNDLED: false

DIRECT_CONSUMER:
  Q3.RouteB.D0Pstar.selectedFamily_eq_muntzApproximation_add_objectResidualCoordinate

SOLE_RUNNER_UP:
  G6_S2_FULL_L2_FOURIER_MELLIN_RESIDUAL_BRIDGE
RUNNER_UP_AUTHORIZED: false

STOP: G6_S2_NAMED_OBJECT_RESIDUAL_CROSSWALK_CONTRACT_MISSING
SUCCESS: G6_S2_NAMED_OBJECT_RESIDUAL_CONDITIONAL_RECEIVER_MATERIALIZED

PHASE_KEY_CHANGE: false
NEW_CHAT: false
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 4

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ARISTOTLE_SUBMISSION: NONE
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

## 1. Source and Phase-4A verification

The branch reference resolves exactly to `8487d4dc3557b8bfe4d57f61c3b67508d7d19f23`. The commit records precisely the current residual fork: the missing bridge is the exact (L^2(du/u)) Fourier reconstruction plus the conversion of its bounded Mellin coordinate to `Gwin`; it explicitly forbids renaming `rawFplus - scaledGwin` as an object residual.   `[ABSTRACT][PAPER]`

The active Spine records the supplied `CODEX_CONTROL.md` SHA-256, active status, Codex trigger ownership, `CHALLENGER_NOT_RH`, Bus 010 `VOID`, and PX/RH as the sole owner boundary.  `[ABSTRACT][PAPER]`

The Arsenal deck and mandate were fetched. The deck’s byte SHA-256 is independently recorded by its materialization ledger as `018dbf6b…3839d`; the five standing attack-duals are accepted.    `[ABSTRACT][PAPER]`

Phase 4A is intact at the current pin. Its production file fixes:

* `selectedPairIndex S k = (parent (extract k)).1`;
* the source trial as the same selected `prolateCombination`;
* the Müntz coordinate as `Gwin h λ (-I*z)`;
* the raw coordinate as `rawFplus ... (-z)`;
* the exact `sTrial_m_N` normalization;
* the defect as raw coordinate minus scaled full-window coordinate.

It proves only the algebraic selected-family decomposition and explicitly proves no zero, limit, or `SlotS2` statement.  `[COFINAL_FAMILY][LEAN]`

The Phase-4A closeout records direct Lean, target build 7774, full build 7817, `q3_check`, zero holes, zero forbidden imports, 67/67 orchestration tests, standard-triple axioms, and all four semantic plants firing. Its manifest records the answer SHA-256 `322deb…005`.   `[COFINAL_FAMILY][LEAN]`

Goal 055 remains the held draft outside the bus, and the route state remains challenger/not-RH with no promotion or RH claim.  `[ABSTRACT][PAPER]`

## 2. Exact missing implication

Let

[
i_k:=\operatorname{selectedPairIndex}(S,k),\qquad
h_k:=\operatorname{selectedProlateTrial}(S,k),
]

and let (hLp_k) be the exact stored `S.source.eStar_memLp i_k`.

The missing implication is exactly:

[
\boxed{
\begin{aligned}
&\operatorname{selectedGalerkinCoordinateDefect}(S,k,z)\
&\quad =
\int_{I_{i_k}}
\Bigl[
sTrial_{i_k},
\bigl(P_{i_k,N_k}gTrial_{i_k}-gTrial_{i_k}\bigr)
\Bigr](u),
u^{-iz},\frac{du}{u}.
\end{aligned}}
]

Equivalently, in project terms:

```text
selectedGalerkinCoordinateDefect S k z
=
MellinCoordinate_(dStar|I_m)
  ((selectedTrialNormalizer S k : ℂ) •
    ((gTrial_m_N i_k h_k hLp_k : H_m i_k) -
      gTrial_m i_k h_k hLp_k))
  z
```

for every `k : ℕ` and `z : ℂ`.

This sign is forced. Phase 4A defines:

```text
defect = normalized projected coordinate - normalized full-window coordinate
```

so the object residual must be:

```text
projection - full object
```

not its negative.

The measure and exponent are also forced. `Gwin h Λ (-I*z)` is a Lebesgue integral with kernel (u^{-iz-1}), whereas `dStar` is (du/u); therefore the corresponding `H_m` coordinate uses (u^{-iz}) against `dStar`. `Gwin`, `dStar`, `I_m`, the Galerkin projection, and the normalized coefficient row are all currently separate exact definitions.     `[COFINAL_FAMILY][LEAN]`

## 3. Decision among A–D

| Path  | Verdict      | Reason                                                                                                       |
| ----- | ------------ | ------------------------------------------------------------------------------------------------------------ |
| **A** | Deferred     | Mathematically coherent, but not one smallest bounded theorem transaction at this pin                        |
| **B** | **Selected** | Names exactly the absent object-first identity and yields a useful conditional receiver without hiding decay |
| **C** | Rejected     | No type, sign, source, or carrier contradiction makes the route incoherent                                   |
| **D** | Rejected     | No small `#check`-style harness can decide A versus B without beginning the substantive proof itself         |

### Why A is not the selected transaction

The current repository provides the objects, but the full bridge would require at least four independent new theorem families:

1. **Weighted Fourier orthonormality**
   [
   \langle V_{n,m},V_{r,m}\rangle_{L^2(du/u)}
   =\delta_{nr}.
   ]

2. **Finite reconstruction of the orthogonal projection**
   [
   P_{m,N}f
   ========

   \sum_{|n|\le N}\langle V_{n,m},f\rangle V_{n,m}.
   ]

3. **Projection-coordinate to raw-transform transport**, identifying the coordinate of that reconstructed `Lp` vector with the already-proved finite logarithmic Fourier integral and hence with `rawFplus`.

4. **Unprojected-coordinate to `Gwin` transport**, including:

   * `dStar = du/u` on the positive window;
   * `Icc` versus `Ioo` null endpoints;
   * the logarithmic coordinate orientation;
   * the complex kernel (u^{-iz});
   * `Lp` representative/integrability handling.

The project currently defines `E_m_N` only as the span of the `V_n_m` family and `P_m_N` as an abstract orthogonal projection. It proves a single (V_0)-overlap preservation theorem and norm contraction, but no arbitrary Fourier reconstruction theorem.   `[ABSTRACT][LEAN]`

`rawFplus_eq_D0_integral` connects the formal coefficient row to `finiteFplusCenteredIntegral`; it does not identify that finite polynomial with the actual projected `Lp` vector.   `[ABSTRACT][LEAN]`

Thus A is a valid program, but selecting it as one local transaction would silently bundle orthonormality, projection reconstruction, weighted measure transport, and Mellin-coordinate identification. Under `MINIMAL_LEMMA`, that is too broad.

### Why D is not decisive

The repository has already established the relevant API-level fact: Mathlib supplies `Lp` inner-product and orthogonal-projection machinery. The uncertainty is not whether symbols typecheck; it is whether the exact weighted Fourier, measure-change, and coordinate identities can be proved with the source conventions.

A tiny harness could only:

* `#check` APIs already known to exist, which changes no belief; or
* attempt `V_n_m` orthonormality, which is already the first substantive lemma of A.

It therefore does not cleanly discriminate A from B.

## 4. Selected conditional contract

Owned file:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarMuntzGalerkinResidualContract.lean
```

Sole production import:

```lean
import Q3.Proofs.RouteB.D0PstarMuntzCenteredCoordinateLock
```

Namespace:

```lean
Q3.RouteB.D0Pstar
```

### 4.1 Literal object residual

```lean
noncomputable def selectedNormalizedGalerkinResidual
    (S : ProlateCanonicalSourceData) (k : ℕ) :
    H_m (selectedPairIndex S k) :=
  let i := selectedPairIndex S k
  let h := selectedProlateTrial S k
  let hLp := S.source.eStar_memLp i
  (selectedTrialNormalizer S k : ℂ) •
    ((gTrial_m_N i h hLp : H_m i) -
      gTrial_m i h hLp)
```

This is the exact source object. It is not defined from `rawFplus`, `Gwin`, or their difference.

### 4.2 Literal residual Mellin coordinate

```lean
noncomputable def selectedGalerkinResidualMellinCoordinate
    (S : ProlateCanonicalSourceData)
    (k : ℕ) (z : ℂ) : ℂ :=
  let i := selectedPairIndex S k
  ∫ u,
      (selectedNormalizedGalerkinResidual S k) u *
        (u : ℂ) ^ (-Complex.I * z)
    ∂(dStar.restrict (I_m i))
```

Minor coercion syntax may be adjusted to the exact Mathlib `Lp` API. The mathematical object, measure, residual order, normalization, and exponent may not change.

### 4.3 Exact conditional input

```lean
def D0PstarMuntzGalerkinResidualCrosswalkContract
    (S : ProlateCanonicalSourceData) : Prop :=
  ∀ k : ℕ, ∀ z : ℂ,
    selectedGalerkinCoordinateDefect S k z =
      selectedGalerkinResidualMellinCoordinate S k z
```

Status:

```text
[COFINAL_FAMILY][CONDITIONAL]
```

This is a named hypothesis, not an axiom and not a proved theorem.

The selected transaction must **not** add any declaration of the form:

```lean
axiom d0PstarMuntzGalerkinResidualCrosswalk ...
```

or:

```lean
theorem d0PstarMuntzGalerkinResidualCrosswalk : ... := by
  sorry
```

### 4.4 Hole-free direct consumer

```lean
theorem selectedFamily_eq_muntzApproximation_add_objectResidualCoordinate
    (S : ProlateCanonicalSourceData)
    (hXW : D0PstarMuntzGalerkinResidualCrosswalkContract S)
    (k : ℕ) (z : ℂ) :
    selectedFamily (canonicalApproximation S.canonical) k z =
      selectedMuntzApproximation S k z +
        selectedCenteringFactor S k *
          selectedGalerkinResidualMellinCoordinate S k (-z) := by
  rw [selectedFamily_eq_muntzApproximation_add_defect]
  rw [hXW k (-z)]
```

This theorem is the **one direct downstream consumer**.

It proves an actual spendable selected-family decomposition, while preserving the residual identity as an explicit hypothesis.

## 5. Object identification and compact-open decay remain separate

The selected contract states only:

```text
formal coordinate defect
=
coordinate of the literal object residual.
```

It does not state:

```text
the residual norm tends to zero;
the residual coordinate tends to zero;
the convergence is locally uniform;
SlotS2 holds.
```

The later analytic condition is separately:

[
\operatorname{TendstoLocallyUniformlyOn}
\left(
k\mapsto
\operatorname{selectedGalerkinResidualMellinCoordinate}(S,k,\cdot)
\right)
0
\quad\text{on the centered strip}.
]

No such condition belongs in this transaction.

The full bridge that would later discharge the selected contract is the sole unauthorized runner-up:

```text
G6_S2_FULL_L2_FOURIER_MELLIN_RESIDUAL_BRIDGE
```

Its required theorem chain is:

```text
V_n_m orthonormality
→ exact projection reconstruction
→ projected L2 coordinate = rawFplus
→ unprojected L2 coordinate = Gwin
→ contract construction
```

Compact-open decay remains a subsequent independent analytic wall even after that chain succeeds.

## 6. Load-bearing plants

### P056K-1 — residual order/sign

Mutation:

```text
gTrial_m - (gTrial_m_N : H_m)
```

instead of:

```text
(gTrial_m_N : H_m) - gTrial_m
```

Required result:

```text
G6_S2_RESIDUAL_SIGN_ORIENTATION_MISMATCH
```

The Phase-4A identity fixes `raw - scaledGwin`; the reversed residual would produce the negative coordinate.

### P056K-2 — parent/extract identity

Mutation:

```text
S.canonical.parent k
```

or:

```text
S.canonical.parent (S.canonical.extract (k + 1))
```

instead of:

```text
S.canonical.parent (S.canonical.extract k)
```

Required result:

```text
G6_S2_RESIDUAL_PARENT_EXTRACT_MISMATCH
```

The source trial, projection carrier, coefficient row, normalizer, raw transform, and `Gwin` window must all use the same literal selected index.

### P056K-3 — measure/kernel orientation

Mutations:

```text
volume.restrict (I_m i)
```

instead of:

```text
dStar.restrict (I_m i)
```

and separately:

```text
(u : ℂ) ^ (Complex.I * z)
```

instead of:

```text
(u : ℂ) ^ (-Complex.I * z).
```

Required result:

```text
G6_S2_RESIDUAL_MEASURE_KERNEL_MISMATCH
```

The (du/u) density accounts for the `-1` in the Lebesgue `Gwin` Mellin exponent, while the negative sign of (iz) is fixed by Phase 4A.

### P056K-4 — normalization deletion

Mutation:

```text
(gTrial_m_N : H_m) - gTrial_m
```

without the scalar `selectedTrialNormalizer`.

Required result:

```text
G6_S2_RESIDUAL_NORMALIZER_MISMATCH
```

The production coefficient row is extracted from the normalized projected object `kTrial_m_N`; omitting `sTrial_m_N` changes the represented object.

These plants mutate four different semantic facts: algebraic order, cofinal carrier, measure/phase convention, and normalization. They cannot all survive one coherent wrong convention.

## 7. Strongest attack

> This transaction merely gives the missing theorem a name. It does not prove any new mathematics.

Correct.

That is why the verdict is `CONDITIONAL`, the success code says **conditional receiver materialized**, and no theorem asserting the contract is authorized.

The transaction has one legitimate purpose: prevent the current definitional difference

```text
rawFplus - scaledGwin
```

from being consumed as though it were already the coordinate of

```text
normalized projection - normalized full object.
```

Those expressions occupy the same scalar coordinate space but are not yet equal in the finer source-object category. This is exactly the C04 distinction. Treating the difference as an object residual without the bridge would be a C10 surrogate substitution. The residual order, index, and coordinate are precommitted before the later proof, as required by C09.  `[ABSTRACT][PAPER]`

The output is therefore representation progress, not proof progress. It is justified only because it reduces the open statement to one exact, typed implication and makes every later consumer expose that implication as a hypothesis.

## 8. Meta closeout

**What became smaller?**

The broad phrase:

```text
build the L2/Fourier/Mellin bridge
```

is compressed to one exact contract:

```text
selectedGalerkinCoordinateDefect
=
Mellin coordinate of
sTrial • (gTrial_m_N - gTrial_m).
```

**What was killed?**

* defining the object residual by `rawFplus - scaledGwin`;
* bundling residual identification with compact-open decay;
* treating Mathlib API availability as proof of the weighted bridge;
* running a non-decisive `#check` harness;
* interpreting Phase 4A as residual or `SlotS2` closure.

**What must not be tried again?**

Do not call the scalar difference a projection residual before the exact coordinate theorem exists. Do not change the residual sign, selected index, measure, kernel orientation, or normalizer to ease the proof.

**Current smallest named gap**

```text
D0PstarMuntzGalerkinResidualCrosswalkContract
```

**Next cheapest decisive mathematical step after this transaction**

The first theorem of the unauthorized runner-up would be:

```text
V_n_m_orthonormal_on_modeSet
```

Its fate would decide whether the full bridge proceeds through Mathlib’s orthonormal-family projection formula or needs a custom logarithmic-window isometry.

**Registered prediction**

```text
P056K-A:
  The conditional receiver compiles in one local pass.

P056K-B:
  The full bridge first stalls at the weighted logarithmic
  orthonormality / measure-change layer, not at the Phase-4A algebra.

P056K-C:
  Compact-open decay remains independent after exact residual
  identification; no algebraic crosswalk alone supplies it.
```

**Prior prediction fate**

```text
Phase-4A prediction:
  a same-index coordinate lock would leave a named Galerkin residual.
  CONFIRMED.

Phase-4B research prediction:
  the next wall is L2/Fourier reconstruction plus du/u-to-Gwin transport.
  CONFIRMED BY SOURCE AUDIT; NOT YET PROVED.
```

```yaml
iteration:
  target: D0PstarMuntzGalerkinResidualCrosswalk
  status: OPEN
  failed_strategy: consume_raw_minus_Gwin_as_if_it_were_an_object_residual
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: D0PstarMuntzGalerkinResidualCrosswalkContract
  invariant_learned: scalar coordinate equality must be derived from the literal normalized projection residual on the same parent_extract index
  forbidden_future_move: define_or_infer_the_object_residual_from_the_coordinate_difference
  next_decisive_test: V_n_m_orthonormal_on_modeSet
  progress_class: REPRESENTATION_PROGRESS
  route_score: 4
```

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS:
  TRY_NAMED_RESIDUAL_CROSSWALK_CONTRACT

TRANSACTION:
  G6_S2_D0PSTAR_MUNTZ_NAMED_RESIDUAL_CROSSWALK_CONTRACT

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: 8487d4dc3557b8bfe4d57f61c3b67508d7d19f23
  expected_CODEX_CONTROL_sha256: fc77ff8d7483c87744f07e8aea3d59b08f9b5340541d3bf414885f239dfafc4e
  expected_phase4A_sha256: ce0226f7bd028449a04cae0dfa28e8998a0e835eba5ec0a56a93f0ae18b073a5

CREATE:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzGalerkinResidualContract.lean

SOLE_IMPORT:
  Q3.Proofs.RouteB.D0PstarMuntzCenteredCoordinateLock

NAMESPACE:
  Q3.RouteB.D0Pstar

REQUIRED_PUBLIC_OBJECTS:
  - selectedNormalizedGalerkinResidual
  - selectedGalerkinResidualMellinCoordinate
  - D0PstarMuntzGalerkinResidualCrosswalkContract

REQUIRED_PUBLIC_THEOREM:
  selectedFamily_eq_muntzApproximation_add_objectResidualCoordinate

REQUIRED_RESIDUAL:
  exact_order: projection_minus_full
  exact_formula: >-
    (selectedTrialNormalizer S k : ℂ) •
    ((gTrial_m_N i h hLp : H_m i) - gTrial_m i h hLp)

REQUIRED_COORDINATE:
  measure: dStar.restrict (I_m i)
  kernel: "(u : ℂ) ^ (-Complex.I * z)"
  index: selectedPairIndex S k
  source_trial: selectedProlateTrial S k

REQUIRED_CONTRACT:
  statement: >-
    for every k and z,
    selectedGalerkinCoordinateDefect S k z =
    selectedGalerkinResidualMellinCoordinate S k z
  status: EXPLICIT_HYPOTHESIS_NOT_PROVED
  declaration_kind: Prop_definition
  axiom_or_global_assumption: forbidden

RECEIVER_PROOF_ROUTE:
  - rewrite selectedFamily_eq_muntzApproximation_add_defect
  - rewrite the explicit contract at k and -z
  - no analytic estimate
  - no limit argument

DO_NOT_BUNDLE:
  - V_n_m orthonormality
  - orthogonal-projection reconstruction
  - dStar/log-coordinate change of variables
  - Gwin integral conversion proof
  - residual norm convergence
  - compact-open residual decay
  - Rminus or Rplus convergence
  - SlotS2

MANDATORY_PLANTS:
  P056K_1_RESIDUAL_SIGN:
    mutation: reverse projection_minus_full
    expected: G6_S2_RESIDUAL_SIGN_ORIENTATION_MISMATCH

  P056K_2_PARENT_EXTRACT:
    mutation: use parent_k_or_shifted_extract
    expected: G6_S2_RESIDUAL_PARENT_EXTRACT_MISMATCH

  P056K_3_MEASURE_ORIENTATION:
    mutations:
      - replace_dStar_by_volume
      - replace_minus_I_z_by_plus_I_z
    expected: G6_S2_RESIDUAL_MEASURE_KERNEL_MISMATCH

  P056K_4_NORMALIZER:
    mutation: delete_selectedTrialNormalizer
    expected: G6_S2_RESIDUAL_NORMALIZER_MISMATCH

VALIDATION:
  - verify HEAD and all source hashes before edit
  - lake env lean q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzGalerkinResidualContract.lean
  - target build
  - full build
  - bash scripts/q3_check.sh q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzGalerkinResidualContract.lean
  - hole scan for sorry admit exact? native_decide axiom opaque
  - forbidden import scan for aristotle_output and ACTIVE RequestProject modules
  - verify no theorem proves the contract without hypotheses
  - fire all four temporary mutations
  - remove temporary mutation files
  - strict Spine validation
  - proof database import
  - "#print axioms Q3.RouteB.D0Pstar.selectedFamily_eq_muntzApproximation_add_objectResidualCoordinate"
  - expected axioms exactly [propext, Classical.choice, Quot.sound]
  - git diff --check
  - exact git status report

STOP:
  G6_S2_NAMED_OBJECT_RESIDUAL_CROSSWALK_CONTRACT_MISSING

SUCCESS:
  G6_S2_NAMED_OBJECT_RESIDUAL_CONDITIONAL_RECEIVER_MATERIALIZED

SOLE_RUNNER_UP_NOT_AUTHORIZED:
  G6_S2_FULL_L2_FOURIER_MELLIN_RESIDUAL_BRIDGE

FORBIDDEN:
  - declare the contract as an axiom
  - prove it with sorry admit exact? native_decide or opaque
  - define residual from rawFplus_minus_scaledGwin
  - reverse the residual sign
  - change parent_extract
  - change dStar to volume
  - change the Mellin exponent orientation
  - omit sTrial_m_N
  - assert compact-open decay
  - assert SlotS2
  - edit Q3.Main
  - edit held Goal 055
  - create Bus 010
  - submit Aristotle
  - promote Route B
  - make PX or RH claim
  - open a fresh Proshka chat

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  bus_010: VOID
  goal_055: HOLD
  aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
```
