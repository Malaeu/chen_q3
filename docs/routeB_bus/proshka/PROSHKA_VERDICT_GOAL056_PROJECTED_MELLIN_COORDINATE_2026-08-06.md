# STATUS: OPEN — ADDITIVE-FIRST PROJECTED MELLIN COORDINATE BRIDGE SELECTED

```yaml
PRIMARY: G6_S2_SELECTED_PROJECTED_MELLIN_COORDINATE_BRIDGE_SELECTED
PRIMARY_COUNT: 1

OPERATIVE_CLASS: TRY_G6_S2_D0_ADDITIVE_FIRST_PROJECTED_MELLIN_COORDINATE
OPERATIVE_CLASS_COUNT: 1
SELECTED_ROUTE: A_ADDITIVE_FIRST

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  PIN: 9a8fb23054ab1f80209eb9f8920fc692d393977f
  ORIGIN_HEAD_EQUALS_PIN: true
  PIN_COMMIT: "[MacOS][rh_clean][Docs] Research Goal 056 projected Mellin coordinate"

PHASE:
  SAME_SIX_FIELD_PHASE_KEY: true
  SAME_LIVING_CHAT: true
  PHASE_KEY_CHANGE: false
  NEW_CHAT: false

PHASE_4D:
  RESULT: G6_S2_P_M_N_FINITE_FOURIER_RECONSTRUCTION_PROVED
  FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0FiniteProjectionReconstruction.lean
  SHA256: 4f19de8c695450691266171ce05b7343c5cbe16213eb71f3b40d2b119bdcaa8d
  PROJECTION_GEOMETRY: CLOSED
  PUBLIC_THEOREMS: 1
  PUBLIC_DEFINITIONS: 0

SELECTED_TRANSACTION:
  NAME: G6_S2_D0_SELECTED_PROJECTED_MELLIN_COORDINATE_RAW_TRANSFORM
  OWNED_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarProjectedMellinCoordinate.lean
  NAMESPACE: Q3.RouteB.D0Pstar
  PROJECT_IMPORTS: 2
  PUBLIC_DEFINITIONS: 1
  PUBLIC_THEOREMS: 2
  PRIVATE_PRODUCTION_DECLARATIONS: 0

PUBLIC_DEFINITION:
  selectedProjectedMellinCoordinate

PUBLIC_THEOREMS:
  - kTrial_m_N_coeFn_ae_eq_finiteLogFourierTrial_logWindow
  - selectedProjectedMellinCoordinate_eq_selectedRawTransformCoordinate

STOP: G6_S2_SELECTED_PROJECTED_MELLIN_COORDINATE_RAW_TRANSFORM_MISSING
SUCCESS: G6_S2_SELECTED_PROJECTED_MELLIN_COORDINATE_EQ_RAW_TRANSFORM_PROVED

SOLE_NEXT_NODE_NOT_AUTHORIZED:
  selectedFullMellinCoordinate_eq_selectedGwinTransformCoordinate

PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ARISTOTLE_SUBMISSION: NONE
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

## 1. Source-lock and closed-gate audit

`origin/rh_clean` resolves exactly to `9a8fb23054ab1f80209eb9f8920fc692d393977f`, with the stated research-only commit message. That commit records the present projected-coordinate fork and does not modify production mathematics.   `[ABSTRACT][PAPER]`

The Phase-4D production file at this pin contains exactly the unconditional theorem

```lean
theorem coe_P_m_N_apply_eq_sum_inner_V_n_m_smul
    (i : PairIndex) (f : H_m i) :
    (P_m_N i f : H_m i) =
      ∑ n ∈ modeSet i,
        inner ℂ (V_n_m i n) f • V_n_m i n
```

on the literal `P_m_N`, `E_m_N`, `modeSet`, and `V_n_m` objects. Its proof uses `OrthonormalBasis.span` and `orthogonalProjection_eq_sum`; it introduces no auxiliary Fourier carrier.  `[ABSTRACT][LEAN]`

The tracked Phase-4D closeout records the supplied production SHA-256, direct Lean, target/full builds, `q3_check`, five fired plants, standard-triple axioms, 67/67 tests, proof-DB import, strict Spine, and the three SQLite integrity checks. It explicitly names the present projected-Mellin identity as the sole next consumer.  `[ABSTRACT][LEAN]`

Phase 4A remains source-locked to one literal selected index

[
i_k=\bigl(S.\mathrm{canonical.parent}(S.\mathrm{canonical.extract}\ k)\bigr).1,
]

with:

```text
selectedRawTransformCoordinate S k z
  = rawFplus S.canonical.kTrial i_k (-z)

selectedGwinTransformCoordinate S k z
  = Gwin h_k (lambda_m i_k) (-I*z).
```

It deliberately leaves their difference as `selectedGalerkinCoordinateDefect`.   `[COFINAL_FAMILY][LEAN]`

Phase 4B defines the literal normalized residual from the **object difference**

```text
selectedTrialNormalizer • (projected trial - full trial)
```

and keeps its scalar-coordinate identification as an explicit `Prop` hypothesis. No axiom or theorem proves that contract.   `[COFINAL_FAMILY][LEAN]`

Phase 4C supplies exactly the unrestricted logarithmic change of variables

```lean
integral_comp_logWindow_dStar
```

and literal orthonormality of `V_n_m`; the closeout records the supplied SHA-256 and all stated validation gates.   `[ABSTRACT][LEAN]`

Stage 3 fixes both normalization and coefficient orientation:

```lean
kTrial_m_N = sTrial_m_N • gTrial_m_N

c_n ... n = inner ℂ (V_n_m i n) (kTrial_m_N ... : H_m i).
```

Thus a conjugated coefficient row or an unnormalized projection is not a harmless equivalent representation.  `[ABSTRACT][LEAN]`

The runtime still records the same Goal-056 G6/S2 phase key and the same conversation ID, with no phase rollover or fresh-chat event.  `[COFINAL_FAMILY][PAPER]`

The supplied SHA-256 values are corroborated by tracked closeouts and manifest entries. I inspected the current file contents but did not independently rerun `sha256sum` or Lean in this adjudication.

## 2. Route comparison

| Route                             | Actual theorem reduction                                                                                                                          |                                                              Diagnostic quality |                  Public cost | Verdict                     |
| --------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------: | ---------------------------: | --------------------------- |
| **A. Additive-first**             | First identify the normalized projected `Lp` representative a.e. with the exact finite logarithmic Fourier trial; then perform one Mellin wrapper | High: separates projection/representative failure from phase/reflection failure | One definition, two theorems | **Selected**                |
| **B. Direct selected wrapper**    | Expand the selected object, representatives, finite sum, `cpow`, phase, and raw reflection inside one theorem                                     |                          Low: seven convention seams fail at one final equality |  One definition, one theorem | Rejected by `MINIMAL_LEMMA` |
| **C. Weakened/scalar substitute** | Define the projected coordinate from `rawFplus` or a finite coefficient sum                                                                       |                                  Vacuous: it assumes the bridge being requested |          Superficially cheap | Forbidden by **C04/C10**    |

Route A remains one bounded file and exposes only one helper theorem before the selected theorem. The helper proves an actual a.e. identity for the literal normalized projected object; it is not scaffolding or a future budget.

## 3. Exact mathematical object

### Selected projected Mellin coordinate

```lean
noncomputable def selectedProjectedMellinCoordinate
    (S : ProlateCanonicalSourceData)
    (k : ℕ) (z : ℂ) : ℂ :=
  let i := selectedPairIndex S k
  let h := selectedProlateTrial S k
  let hLp := S.source.eStar_memLp i
  let hNonzero := S.source.trialNonzero i
  ∫ u : ℝ,
      (kTrial_m_N i h hLp hNonzero : H_m i) u *
        (u : ℂ) ^ (-Complex.I * z)
    ∂(dStar.restrict (I_m i))
```

`[COFINAL_FAMILY][CONDITIONAL]`

This is the coordinate of the literal normalized projected trial:

[
kTrial_{m,N}
============

sTrial_{m,N},P_{m,N}gTrial_m.
]

It is not defined from `rawFplus`, `finiteRawCenteredIntegral`, `selectedGalerkinCoordinateDefect`, or `Gwin`.

That object choice is mandatory. Defining the new scalar from the desired right-hand side would close the theorem by construction while leaving the object-first bridge open—precisely the C04/C10 failure that Phase 4B was introduced to prevent.

## 4. Exact additive helper theorem

```lean
theorem kTrial_m_N_coeFn_ae_eq_finiteLogFourierTrial_logWindow
    (i : PairIndex)
    (hTrial_m : ℝ → ℂ)
    (hE_star :
      MemLp (E_star hTrial_m) 2 (dStar.restrict (I_m i)))
    (hTrialNonzero : TrialNonzero i hTrial_m hE_star) :
    (fun u : ℝ =>
      (kTrial_m_N i hTrial_m hE_star hTrialNonzero : H_m i) u)
      =ᵐ[dStar.restrict (I_m i)]
    (fun u : ℝ =>
      finiteLogFourierTrial
        (L_m i)
        (modeSet i)
        (c_n i hTrial_m hE_star hTrialNonzero)
        (Real.log (lambda_m i * u))) := by
  ...
```

`[ABSTRACT][CONDITIONAL]`

This theorem carries all of the source structure that matters:

* literal normalized projection;
* literal full finite sector `modeSet i`;
* coefficient orientation `inner(V_n,kTrial)`;
* exact logarithmic coordinate `log(lambda_m i * u)`;
* a.e., rather than false pointwise, equality of `Lp` representatives.

It says nothing about Mellin kernels, `rawFplus`, `Gwin`, residuals, or limits.

## 5. Exact target theorem

```lean
theorem selectedProjectedMellinCoordinate_eq_selectedRawTransformCoordinate
    (S : ProlateCanonicalSourceData)
    (k : ℕ) (z : ℂ) :
    selectedProjectedMellinCoordinate S k z =
      selectedRawTransformCoordinate S k z := by
  ...
```

`[COFINAL_FAMILY][CONDITIONAL]`

There is **no extra minus sign in the theorem arguments**. The required reflection is already built into the right-hand side:

```text
selectedRawTransformCoordinate S k z
  = rawFplus ... (-z).
```

## 6. Explicit sign and centering derivation

Fix

[
i=i_k,\qquad
L=L_m(i)=\log m,\qquad
\lambda=\lambda_m(i)=\sqrt m,
]

and set

[
x=\log(\lambda u).
]

Since (\lambda^2=m),

[
\log\lambda=\frac{L}{2},
\qquad
\log u=x-\frac L2.
]

For (u\in I_m(i)), one has (u>0). Therefore Mathlib’s complex power is on the positive-real logarithm branch, and

[
\begin{aligned}
(u:\mathbb C)^{-iz}
&=\exp!\bigl((-iz)\log u\bigr)\
&=\exp!\left((-iz)\left(x-\frac L2\right)\right)\
&=\exp!\left(\frac{izL}{2}\right)\exp(-izx).
\end{aligned}
]

The production source convention independently records this same formula:

[
T_m(\kappa_m g)(z)
==================

\lambda^{iz}\int_0^L g(x)e^{-izx},dx,
]

with the centering phase forced by (x=\log(\lambda u)).  `[ABSTRACT][PAPER]`

Applying the additive helper and the Phase-4C transport gives

[
\begin{aligned}
\operatorname{selectedProjectedMellinCoordinate}(S,k,z)
&=
e^{izL/2}
\int_0^L
\operatorname{finiteLogFourierTrial}(x)e^{-izx},dx\
&=
\operatorname{finiteRawCenteredIntegral}(L,\mathrm{modeSet},c,z)\
&=
\operatorname{proposition59RawTransform}(L,\mathrm{modeSet},c,z).
\end{aligned}
]

The raw-integral crosswalk proves exactly this centered raw formula, including removable lattice values. It also proves

```text
finiteFplusCenteredIntegral ... w
  = finiteRawCenteredIntegral ... (-w).
```

`[ABSTRACT][LEAN]`

Finally,

```text
rawFplus D i w
  = proposition59RawTransform L (modeSet i) (D.kTrial i) (-w).
```

Therefore, at (w=-z),

[
rawFplus(D,i,-z)
================

\operatorname{proposition59RawTransform}(L,\mathrm{modeSet},c,z),
]

which is exactly `selectedRawTransformCoordinate S k z`. The existing `rawFplus_eq_D0_integral` theorem and `selectedCanonical_kTrial` supply the last coefficient-row rewrite.   `[COFINAL_FAMILY][LEAN]`

## 7. Exact proof route

### 7.1 Additive representative theorem

1. Install the same `FiniteDimensional` and `CompleteSpace` instances for `E_m_N i` used by the existing D0 projection layer.
2. Let

   ```lean
   kE : E_m_N i := kTrial_m_N i hTrial_m hE_star hTrialNonzero
   ```

   and let `kH : H_m i := kE`.
3. Prove that the literal projection fixes `kH`. The pinned Mathlib characterization

   ```lean
   Submodule.eq_starProjection_of_mem_of_inner_eq_zero
   ```

   applies using `kE.property` and the trivial equality `kH - kH = 0`. The `orthogonalProjection`/`starProjection` relation is definitional in the pinned API.  `[ABSTRACT][LEAN]`
4. Apply

   ```lean
   coe_P_m_N_apply_eq_sum_inner_V_n_m_smul i kH
   ```

   and rewrite the fixed-projection left side.
5. Fold the coefficients directly with `c_n`; no conjugation lemma or projection-coefficient repair is needed because `c_n` is definitionally `inner(V_n,kTrial)`.
6. Use `MemLp.coeFn_toLp` for each finite mode and a finite intersection of the resulting a.e. equalities.
7. Simplify the finite sum to `finiteLogFourierTrial`.

No projection geometry is reproved; Phase 4D is consumed exactly once.

### 7.2 Multiplicative wrapper

1. Unfold `selectedProjectedMellinCoordinate`.
2. Rewrite the normalized projected representative using the additive helper and `integral_congr_ae`.
3. Combine with membership a.e. in `I_m i` to obtain (u>0).
4. Rewrite the kernel using:

   ```lean
   Complex.cpow_def_of_ne_zero
   Complex.ofReal_log
   ```

   only under that positive-window hypothesis. The pinned Mathlib API gives the exact nonzero complex-power formula.  `[ABSTRACT][LEAN]`
5. Apply:

   ```lean
   integral_comp_logWindow_dStar
   ```

   to the complete additive integrand.
6. Convert the `Icc 0 L` set integral to the oriented interval integral using:

   ```lean
   MeasureTheory.integral_Icc_eq_integral_Ioc
   intervalIntegral.integral_of_le
   ```
7. Fold `finiteRawCenteredIntegral`.
8. Rewrite through:

   ```lean
   finiteFplusCenteredIntegral_eq_raw_neg
   rawFplus_eq_D0_integral
   selectedCanonical_kTrial
   ```
9. Close by unfolding `selectedRawTransformCoordinate`.

The pinned Mathlib Mellin implementation uses the same safe pattern—`cpow_def_of_ne_zero` followed by `Complex.ofReal_log` under positivity—so this is an existing v4.26-compatible route, not an invented API guess.  `[ABSTRACT][LEAN]`

## 8. K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  selected_index:
    S.canonical.parent (S.canonical.extract k)

  projected_object:
    kTrial_m_N
      (selectedPairIndex S k)
      (selectedProlateTrial S k)
      stored_eStar_memLp
      stored_trialNonzero

  ambient_carrier:
    H_m (selectedPairIndex S k)

  measure:
    dStar.restrict (I_m (selectedPairIndex S k))

  multiplicative_kernel:
    "(u : ℂ) ^ (-Complex.I * z)"

  additive_coordinate:
    "x = Real.log (lambda_m i * u)"

  additive_mode_family:
    V_n_m i

  coefficient_row:
    c_n i h hLp hNonzero n = inner ℂ (V_n_m i n) kTrial

  finite_sector:
    modeSet i = Finset.Icc (-N) N

  centered_phase:
    "Complex.exp (Complex.I * z * (L_m i : ℂ) / 2)"

  raw_target:
    "rawFplus S.canonical.kTrial i (-z)"

  raw_transform_argument_after_double_reflection:
    z
```

`[COFINAL_FAMILY][CONDITIONAL]`

Changing any field after a plant fires requires a new named transaction.

## 9. Mandatory semantic plants

### `P056N-1 — projection versus full object`

Mutation:

```text
kTrial_m_N
→ selectedTrialNormalizer • gTrial_m
```

Required result:

```text
G6_S2_PROJECTED_MELLIN_FULL_OBJECT_SUBSTITUTION
```

The full object belongs to the later `Gwin` coordinate theorem, not this one.

### `P056N-2 — normalization`

Mutation:

```text
kTrial_m_N
→ gTrial_m_N
```

Required result:

```text
G6_S2_PROJECTED_MELLIN_NORMALIZATION_MISMATCH
```

The raw row is the coefficient row of the normalized projected trial.

### `P056N-3 — coefficient conjugation`

Mutation:

```text
inner ℂ (V_n_m i n) kTrial
→ inner ℂ kTrial (V_n_m i n)
```

Required result:

```text
G6_S2_PROJECTED_MELLIN_COEFFICIENT_CONJUGATION_MISMATCH
```

Use the synthetic control (f=iV_0): the two coefficients are (i) and (-i).

### `P056N-4 — positive mode boundary`

Mutation:

```text
modeSet i
→ (modeSet i).erase (i.N : ℤ)
```

Required result:

```text
G6_S2_PROJECTED_MELLIN_MODESET_BOUNDARY_MISMATCH
```

Use the control (N=1,\ f=V_1).

### `P056N-5 — measure/window`

Two mutations under one semantic plant:

```text
dStar.restrict (I_m i)
→ volume.restrict (I_m i)
```

and

```text
I_m i = Icc lambda⁻¹ lambda
→ a one-sided or shifted window
```

Required result:

```text
G6_S2_PROJECTED_MELLIN_DSTAR_WINDOW_MISMATCH
```

The logarithmic Jacobian or the exact image `[0,L]` must fail.

### `P056N-6 — centered phase`

Mutation:

```text
exp(+I*z*L/2)
→ 1
```

or to `exp(-I*z*L/2)`.

Required result:

```text
G6_S2_PROJECTED_MELLIN_CENTERING_PHASE_MISMATCH
```

### `P056N-7 — raw reflection`

Mutation:

```text
rawFplus ... (-z)
→ rawFplus ... z
```

Required result:

```text
G6_S2_PROJECTED_MELLIN_RAW_REFLECTION_MISMATCH
```

Use a non-even one-mode coefficient row; the constant mode alone is not a sufficient reflection plant.

These plants mutate seven independent semantic facts. They cannot all pass under one coherent alternate convention.

## 10. Scope boundary

Only the following are authorized:

```text
1. one additive a.e. representative theorem;
2. one object-first selected coordinate definition;
3. one projected-coordinate = selected-raw-coordinate theorem.
```

Not authorized:

```text
selected full-object coordinate = Gwin;
raw/Gwin equality;
Phase-4B contract proof;
residual-coordinate algebra;
residual norm convergence;
compact-open decay;
Rminus or Rplus decay;
strict SlotS2;
Aristotle;
Q3.Main;
route promotion;
PX or RH claim.
```

The sole next node, not authorized here, is:

```text
selectedFullMellinCoordinate_eq_selectedGwinTransformCoordinate
```

That theorem must use the unprojected `gTrial_m`/`E_star` object. It must not be folded into the present projection theorem.

## 11. Dependency edge removed

Before this transaction, the route has the open edge:

```text
literal normalized projected Lp object
  → its source-locked finite raw transform coordinate.
```

After success, the edge becomes:

```text
Mellin coordinate of kTrial_m_N at u^(-i*z)
  =
rawFplus of its exact coefficient row at -z.
```

This is **PROOF_PROGRESS**:

* the theorem is unconditional;
* it consumes Phase 4D;
* it introduces no assumption or certificate;
* it proves equality of the required source object and scalar functional;
* it removes the projection-to-transform dependency rather than naming it.

## 12. Strongest attack

> The proposed theorem may merely reproduce `rawFplus` under a new name.

It does not. The new definition contains only:

```text
kTrial_m_N;
its Lp representative;
dStar;
I_m;
complex power.
```

It contains no `rawFplus`, coefficient polynomial, Proposition-5.9 kernel, or `Gwin`.

The second attack is more serious:

> `Complex.cpow` is branch-sensitive. The identity
> (u^{-iz}=e^{izL/2}e^{-izx}) is invalid if it is rewritten globally on (\mathbb R).

Correct. The proof is legal only after restricting a.e. to `I_m`, proving (u>0), and then invoking the positive-real logarithm theorem. A global simplification or a proof that ignores the restricted measure must fail with:

```text
G6_S2_PROJECTED_MELLIN_CPOW_BRANCH_GAP
```

No repair by redefining the kernel is permitted.

## 13. Meta closeout

**What became smaller?**

The remaining full residual bridge is decomposed into:

```text
projected coordinate = raw transform       ← selected now
full-object coordinate = Gwin              ← separate
linearity of coordinate on projected-full  ← later algebra
compact-open residual decay                ← separate analysis
```

**What was rejected?**

* one opaque direct theorem bundling every seam;
* defining the projected coordinate from `rawFplus`;
* using the full trial in place of the projection;
* treating `Lp` equality as pointwise equality;
* suppressing the centering phase;
* forgetting the double reflection.

**Current smallest named gap:**

```text
G6_S2_SELECTED_PROJECTED_MELLIN_COORDINATE_RAW_TRANSFORM_MISSING
```

**Registered prediction:**

```text
P056N-A:
  the additive representative theorem and selected wrapper close in one file.

P056N-B:
  the main Lean friction is the finite a.e. representative normalization and
  positive-real cpow rewrite, not projection geometry.

P056N-C:
  after this theorem, the true analytic seam is the full E_star/Gwin coordinate;
  compact-open decay remains independent.
```

**Fate of prior predictions:**

```text
Phase-4C prediction:
  projection reconstruction would be smaller than Gwin conversion.
  CONFIRMED.

Phase-4D prediction:
  the next leaf is projected Mellin coordinate = selected raw transform.
  CONFIRMED.

Phase-4B prediction:
  compact-open decay remains separate after exact object identification.
  STILL CONFIRMED.
```

```yaml
iteration:
  target: selected_projected_Mellin_coordinate
  status: OPEN
  failed_strategy: direct_wrapper_bundling_representative_phase_and_reflection_seams
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: G6_S2_SELECTED_PROJECTED_MELLIN_COORDINATE_RAW_TRANSFORM_MISSING
  invariant_learned: the exact normalized projection and raw coefficient transform agree only after an a.e. log-window and centered-phase transport
  forbidden_future_move: define_the_projected_coordinate_from_rawFplus_or_rewrite_cpow_outside_the_positive_window
  next_decisive_test: direct_Lean_compile_of_the_additive_ae_helper_with_all_seven_plants
  progress_class: PROOF_PROGRESS
  route_score: 5
```

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS:
  TRY_G6_S2_D0_ADDITIVE_FIRST_PROJECTED_MELLIN_COORDINATE

TRANSACTION:
  G6_S2_D0_SELECTED_PROJECTED_MELLIN_COORDINATE_RAW_TRANSFORM

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

EXECUTION:
  authorized_after_relay: true
  use_existing_phase_chat: true
  fresh_chat: forbidden
  Aristotle_submission: NONE

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: 9a8fb23054ab1f80209eb9f8920fc692d393977f

  expected_phase4D:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/D0FiniteProjectionReconstruction.lean
    sha256: 4f19de8c695450691266171ce05b7343c5cbe16213eb71f3b40d2b119bdcaa8d

  expected_centered_lock:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzCenteredCoordinateLock.lean
    sha256: ce0226f7bd028449a04cae0dfa28e8998a0e835eba5ec0a56a93f0ae18b073a5

  expected_phase4B_contract:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzGalerkinResidualContract.lean
    sha256: 1f9b0f16210271fc699107f991a244421d98bbdafd695d5a585dae4aca4f73ff
    modify: false
    import_into_new_file: false

  expected_phase4C:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/D0LogWindowMeasureTransport.lean
    sha256: 59c6d9a3a3a3c77427997665216e3ff797b9e2dc925cb63e5e9e6df0df64905b

  expected_stage3:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/D0KTrialStage3.lean
    sha256: 924027a3dd9b95e75c776db552ad37779ed8dd75a7924d744a39cb1a613ebdfa

ON_SOURCE_MISMATCH:
  stop: G6_S2_PROJECTED_MELLIN_SOURCE_LOCK_MISMATCH
  edit_files: false

CREATE:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarProjectedMellinCoordinate.lean

IMPORTS_EXACT:
  - Q3.Proofs.RouteB.D0FiniteProjectionReconstruction
  - Q3.Proofs.RouteB.D0PstarMuntzCenteredCoordinateLock

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE:
  definitions: 1
  theorems: 2
  private_production_declarations: 0

PUBLIC_DEFINITION: |
  noncomputable def selectedProjectedMellinCoordinate
      (S : ProlateCanonicalSourceData)
      (k : ℕ) (z : ℂ) : ℂ :=
    let i := selectedPairIndex S k
    let h := selectedProlateTrial S k
    let hLp := S.source.eStar_memLp i
    let hNonzero := S.source.trialNonzero i
    ∫ u : ℝ,
        (kTrial_m_N i h hLp hNonzero : H_m i) u *
          (u : ℂ) ^ (-Complex.I * z)
      ∂(dStar.restrict (I_m i))

PUBLIC_HELPER_THEOREM: |
  theorem kTrial_m_N_coeFn_ae_eq_finiteLogFourierTrial_logWindow
      (i : PairIndex)
      (hTrial_m : ℝ → ℂ)
      (hE_star :
        MemLp (E_star hTrial_m) 2 (dStar.restrict (I_m i)))
      (hTrialNonzero : TrialNonzero i hTrial_m hE_star) :
      (fun u : ℝ =>
        (kTrial_m_N i hTrial_m hE_star hTrialNonzero : H_m i) u)
        =ᵐ[dStar.restrict (I_m i)]
      (fun u : ℝ =>
        finiteLogFourierTrial
          (L_m i)
          (modeSet i)
          (c_n i hTrial_m hE_star hTrialNonzero)
          (Real.log (lambda_m i * u))) := by
    ...

PUBLIC_TARGET_THEOREM: |
  theorem selectedProjectedMellinCoordinate_eq_selectedRawTransformCoordinate
      (S : ProlateCanonicalSourceData)
      (k : ℕ) (z : ℂ) :
      selectedProjectedMellinCoordinate S k z =
        selectedRawTransformCoordinate S k z := by
    ...

REQUIRED_PROOF_ROUTE:
  additive_helper:
    - install exact FiniteDimensional and CompleteSpace instances for E_m_N i
    - prove P_m_N fixes the coerced kTrial_m_N using exact submodule membership
    - invoke coe_P_m_N_apply_eq_sum_inner_V_n_m_smul exactly once
    - fold c_n without changing inner-product orientation
    - use MemLp.coeFn_toLp on every mode in modeSet
    - combine only finitely many a.e. equalities
    - unfold finiteLogFourierTrial

  selected_wrapper:
    - unfold selectedProjectedMellinCoordinate
    - rewrite by the additive a.e. helper through integral_congr_ae
    - obtain u > 0 from membership in I_m
    - use Complex.cpow_def_of_ne_zero and Complex.ofReal_log
    - prove log(lambda_m i) = L_m i / 2 locally
    - derive u^(-I*z) = exp(I*z*L/2) * exp(-I*z*log(lambda*u))
    - use integral_comp_logWindow_dStar
    - convert Icc integral to interval integral
    - fold finiteRawCenteredIntegral
    - use finiteFplusCenteredIntegral_eq_raw_neg
    - use rawFplus_eq_D0_integral at argument -z
    - rewrite coefficients with selectedCanonical_kTrial
    - unfold selectedRawTransformCoordinate

K6_OBJECT_PRECOMMIT:
  object: normalized_projected_kTrial_m_N
  index: selectedPairIndex_S_k
  measure: dStar_restrict_I_m
  kernel: u_cpow_minus_I_z
  additive_coordinate: log_lambda_mul_u
  finite_sector: full_modeSet_Icc_minusN_N
  coefficient: inner_V_n_kTrial
  phase: exp_plus_I_z_L_over_2
  raw_rhs: rawFplus_at_minus_z

MANDATORY_PLANTS:
  - id: P056N_1_PROJECTED_VS_FULL
    mutation: replace_kTrial_m_N_by_normalized_gTrial_m
    expected: G6_S2_PROJECTED_MELLIN_FULL_OBJECT_SUBSTITUTION

  - id: P056N_2_NORMALIZATION
    mutation: replace_kTrial_m_N_by_gTrial_m_N
    expected: G6_S2_PROJECTED_MELLIN_NORMALIZATION_MISMATCH

  - id: P056N_3_COEFFICIENT_CONJUGATION
    mutation: replace_inner_V_n_kTrial_by_inner_kTrial_V_n
    control: f_eq_I_smul_V0
    expected: G6_S2_PROJECTED_MELLIN_COEFFICIENT_CONJUGATION_MISMATCH

  - id: P056N_4_MODESET_BOUNDARY
    mutation: erase_positive_N
    control: N_eq_1_and_f_eq_V1
    expected: G6_S2_PROJECTED_MELLIN_MODESET_BOUNDARY_MISMATCH

  - id: P056N_5_DSTAR_WINDOW
    mutations:
      - replace_dStar_by_volume
      - replace_exact_symmetric_window_by_shifted_or_one_sided_window
    expected: G6_S2_PROJECTED_MELLIN_DSTAR_WINDOW_MISMATCH

  - id: P056N_6_CENTERING_PHASE
    mutations:
      - delete_exp_plus_I_z_L_over_2
      - flip_phase_sign
    expected: G6_S2_PROJECTED_MELLIN_CENTERING_PHASE_MISMATCH

  - id: P056N_7_RAW_REFLECTION
    mutation: replace_rawFplus_at_minus_z_by_rawFplus_at_z
    control: non_even_single_mode_row
    expected: G6_S2_PROJECTED_MELLIN_RAW_REFLECTION_MISMATCH

VALIDATION:
  - verify HEAD and every supplied SHA before editing
  - lake env lean q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarProjectedMellinCoordinate.lean
  - dedicated target lake build
  - full lake build
  - bash scripts/q3_check.sh q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarProjectedMellinCoordinate.lean
  - scan for sorry admit exact? native_decide axiom opaque Float
  - scan for imports from aristotle_output or ACTIVE RequestProject
  - require exactly one public definition
  - require exactly two public theorems
  - require zero private production declarations
  - fire P056N_1 through P056N_7
  - remove every temporary plant file
  - print axioms for both public theorems
  - require exactly [propext, Classical.choice, Quot.sound]
  - proof database reimport
  - require all new declarations indexed and both theorems marked proven
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
  G6_S2_SELECTED_PROJECTED_MELLIN_COORDINATE_RAW_TRANSFORM_MISSING

SUCCESS:
  G6_S2_SELECTED_PROJECTED_MELLIN_COORDINATE_EQ_RAW_TRANSFORM_PROVED

FAILURE_CODES:
  - G6_S2_PROJECTED_MELLIN_SOURCE_LOCK_MISMATCH
  - G6_S2_PROJECTED_MELLIN_LP_REPRESENTATIVE_GAP
  - G6_S2_PROJECTED_MELLIN_PROJECTION_SELF_GAP
  - G6_S2_PROJECTED_MELLIN_CPOW_BRANCH_GAP
  - G6_S2_PROJECTED_MELLIN_LOG_CENTERING_IDENTITY_GAP
  - G6_S2_PROJECTED_MELLIN_INTERVAL_NORMALIZATION_GAP
  - G6_S2_PROJECTED_MELLIN_FULL_OBJECT_SUBSTITUTION
  - G6_S2_PROJECTED_MELLIN_NORMALIZATION_MISMATCH
  - G6_S2_PROJECTED_MELLIN_COEFFICIENT_CONJUGATION_MISMATCH
  - G6_S2_PROJECTED_MELLIN_MODESET_BOUNDARY_MISMATCH
  - G6_S2_PROJECTED_MELLIN_DSTAR_WINDOW_MISMATCH
  - G6_S2_PROJECTED_MELLIN_CENTERING_PHASE_MISMATCH
  - G6_S2_PROJECTED_MELLIN_RAW_REFLECTION_MISMATCH
  - G6_S2_PROJECTED_MELLIN_PLANT_INERT
  - LEAN_BUILD_FAIL

SOLE_NEXT_NODE_NOT_AUTHORIZED:
  selectedFullMellinCoordinate_eq_selectedGwinTransformCoordinate

FORBIDDEN:
  - modify Phase4A Phase4B Phase4C or Phase4D files
  - import Phase4B contract into the new file
  - define projected coordinate from rawFplus
  - replace projected trial by full trial
  - omit sTrial_m_N normalization
  - reverse complex inner-product orientation
  - prune or shift modeSet
  - replace dStar by volume
  - rewrite complex cpow without proving u > 0
  - omit or flip the centered phase
  - remove the rawFplus reflection
  - prove full-object coordinate equals Gwin
  - prove raw_Gwin equality
  - prove the Phase4B contract
  - prove residual decay
  - prove compact-open convergence
  - prove SlotS2
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
