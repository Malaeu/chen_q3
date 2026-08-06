# STATUS: OPEN — REPAIRED TWO-SUPPLIER PHYSICAL FOURIER RECEIVER SELECTED; SOURCE SUPPLIERS REMAIN OPEN

```yaml
PRIMARY: G6_S2_D0_SELECTED_PHYSICAL_FOURIER_ENERGY_RECEIVER_SELECTED
PRIMARY_COUNT: 1

OPERATIVE_CLASS: TRY_G6_S2_D0_SELECTED_PHYSICAL_FOURIER_ENERGY_RECEIVER
OPERATIVE_CLASS_COUNT: 1

CANDIDATE:
  SELECTED: A_REPAIRED_TWO_SUPPLIER_PHYSICAL_RECEIVER
  B_POINTWISE_ONLY: REJECTED_AS_ARTIFICIAL_BOUNDARY
  C_UNCONDITIONAL_CURRENT_SOURCE: KILLED_AS_UNSUPPORTED_CURRENT_INTERFACE
  D_COUPLED_RATE_RECEIVER: RETAINED_AS_NONACTIVE_FALLBACK
  E_CONSTRUCTIVE_RESELECTION: KILLED_POST_HOC_PATH_CHANGE

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  PIN: 6f28c1cf2668628dfb61f0d7b2daa2eb5d6a7277
  ORIGIN_HEAD_EQUALS_PIN: true
  COMMIT: "[MacOS][rh_clean][Docs] Preflight Goal 056 physical Fourier energy"

HASH_AUDIT:
  D0LogWindowVNMCompletenessBridge:
    EXPECTED_SHA256: 1001bd3c39dcf70ae4d7c31bbc8c0f188d1f9917331b22bb5b0f981cc832e949
    STATUS: VERIFIED_TRACKED_CLOSEOUT_AND_UNCHANGED_CURRENT_CONTENT
  D0HilbertBasisWeightedTail:
    EXPECTED_SHA256: 24956f668098ea0a940ba50ebdd4087d7645114c8c0919a5587f35f10135643c
    STATUS: VERIFIED_TRACKED_CLOSEOUT_AND_UNCHANGED_CURRENT_CONTENT
  D0PstarGalerkinResidualDecay:
    EXPECTED_SHA256: 8fe089afef9e6a43f7b6c7b7b737bc0709e7e35d41ae73a34ab94c49f1f62f63
    STATUS: VERIFIED_TRACKED_CLOSEOUT_AND_UNCHANGED_CURRENT_CONTENT
  D0ProlateKTrialSource:
    EXPECTED_SHA256: 7597910a8cf2160c4ab9786144d25595a6c519395f64fc0846d84a249a96c016
    STATUS: VERIFIED_TRACKED_CLOSEOUT_AND_UNCHANGED_CURRENT_CONTENT
  D0CanonicalApproximation:
    EXPECTED_SHA256: 60409208d26aeae7b4974150bd66ad42da83f09a223f41196dbde7abd3157695
    STATUS: VERIFIED_PHASE4I_LOCK_AND_UNCHANGED_CURRENT_CONTENT
  INSIGHTS:
    EXPECTED_SHA256: 11dfef606e5310b9ce503f389f47f45003df62a052f68c344a0fb612da31adb0
    STATUS: PINNED_CONTENT_AND_COMMIT_DELTA_VERIFIED_NO_MISMATCH
  ROUTE_B_STATE:
    EXPECTED_SHA256: e75457bf7c5e78284e6e434dc94d9e98cc9f870adfc24ce560dfe5374e87aa66
    STATUS: PINNED_CONTENT_VERIFIED_NO_MISMATCH
  BYTE_REHASH_QUALIFICATION:
    code_hashes: independently corroborated by tracked production closeouts
    large_document_hashes: requester disk SHA plus pinned GitHub content checked
    mismatch_observed: false

PREDECESSOR:
  PHASE: 4K
  RESULT: G6_S2_D0_LOG_WINDOW_V_N_M_HILBERT_BASIS_AND_COMPLEMENT_PARSEVAL_PROVED
  REOPENED: false

TRANSACTION:
  NAME: G6_S2_D0_SELECTED_PHYSICAL_FOURIER_ENERGY_RECEIVER
  OWNED_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarPhysicalFourierEnergyControl.lean
  NAMESPACE: Q3.RouteB.D0Pstar

PUBLIC_SURFACE:
  DEFINITIONS: 8
  THEOREMS: 2
  PRIVATE_THEOREMS: 3
  PRIVATE_DEFINITIONS: 0
  TOTAL_DECLARATIONS: 13

STOP: G6_S2_D0_SELECTED_PHYSICAL_FOURIER_ENERGY_RECEIVER_MISSING
SUCCESS: G6_S2_D0_PHYSICAL_FOURIER_ENERGY_AND_BANDWIDTH_TO_PROJECTION_TAIL_PROVED

PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE:
  FIXED_INDEX: ABSTRACT
  SELECTED_PATH: COFINAL_FAMILY_CONDITIONAL
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

DIRECT_DOWNSTREAM_CONSUMER:
  Q3.RouteB.D0Pstar.selectedNormalizedGalerkinResidual_norm_tendsto_zero_of_tail_and_bounded

SOLE_NEXT_NODE_NOT_AUTHORIZED:
  G6_S2_D0_SELECTED_PROLATE_PHYSICAL_FOURIER_ENERGY_SOURCE_SUPPLIER

PHASE_KEY_CHANGE: false
FRESH_CHAT: false
CONVERSATION_ID: 6a72e750-dc60-83eb-946b-61d2073c232b

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ARISTOTLE_SUBMISSION: NONE
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## 1. Source-lock and closed-predecessor audit

The branch ref and the named commit both resolve exactly to `6f28c1cf2668628dfb61f0d7b2daa2eb5d6a7277`. The pinned commit changes only the research entry in `INSIGHTS.md`; it records the physical frequency, the sharp omitted-mode guard, the absence of current source regularity, the failure of bare `PairCofinal` to imply physical-bandwidth cofinality, and the proposed two-supplier receiver.   `[ABSTRACT][PAPER]`

The requester’s source-lock packet states the same pin, seven required SHA-256 values, Phase-4K result, and route boundary. 

Phase 4K is genuinely closed, with the exact production SHA-256, five public declarations, three private load-bearing theorems, eight fired plants, direct/target/full validation, standard axioms, proof-DB import, 67/67 tests, strict Spine, and three clean SQLite checks. It proves the exact two-sided logarithmic (L^2) equivalence, literal completeness of `V_n_m`, and exact complement Parseval identity. It explicitly proves no physical energy, selected rate, `SlotS2`, promotion, PX claim, or RH claim.  `[ABSTRACT][LEAN]`

The current production theorem is literally:

```lean
theorem norm_sub_coe_P_m_N_sq_eq_tsum_complement
    (i : PairIndex) (f : H_m i) :
    ‖f - (P_m_N i f : H_m i)‖ ^ 2 =
      ∑' n : ℤ,
        if n ∈ modeSet i then 0
        else ‖inner ℂ (V_n_m i n) f‖ ^ 2
```

The same file constructs the ordinary-volume Fourier basis with the factor
((\sqrt{L_m})^{-1}), transports it to `H_m`, and proves literal equality to the existing `V_n_m` family.  `[ABSTRACT][LEAN]`

Phase 4J supplies exactly the abstract weighted-tail receiver needed here. Its coefficient convention is `inner ℂ (b n) f`, its retained set is an arbitrary `Finset ℤ`, and its weighted theorem requires nonnegative weights, an outside-band domination inequality, and **explicit summability** of the weighted coefficient row.  `[ABSTRACT][LEAN]`

Phase 4H remains the downstream conditional receiver. It factors the literal normalized residual into inverse projected norm times the unnormalized projection error, and consumes `SelectedProjectionTailDecay` and `SelectedTrialNormalizerBounded` as independent premises.   `[COFINAL_FAMILY][LEAN]`

## 2. What current source data does—and does not—prove

`ProlateKTrialSourceData` now correctly forces the consumed `prolateCombination` to depend only on (m), while `N` remains confined to the finite projection and pair-indexed certificates. Its fields provide source identity, bandwidth identity, `MemLp`, and nonvanishing. They provide no logarithmic weak derivative, periodic (H^1) theorem, weighted Fourier-energy summability, or uniform energy bound.  `[ABSTRACT][LEAN]`

`PairCofinal` is exactly the conjunction

[
m_k\to\infty,
\qquad
N_k\to\infty.
]

It contains no coupling between (N_k) and (L_{m_k}=\log m_k). The selected path remains the literal existing `parent ∘ extract` path.   `[COFINAL_FAMILY][LEAN]`

Phase 4I already fired the decisive counterexample:

[
m_k=2^{(k+1)^2},
\qquad
N_k=k+1.
]

Both coordinates are cofinal, while (N_k/\log m_k\to0). Therefore physical bandwidth does not follow from `PairCofinal`. The same closeout states that the future tail-rate package must keep generic Fourier algebra, bandwidth coupling, and source-specific energy control separate.  `[COFINAL_FAMILY][LEAN]`

Accordingly:

[
\boxed{
\forall S,\ \texttt{SelectedProjectionTailDecay}\ S
}
]

is **not derivable from the current interface**. Its negation has not been proved. The correct classification is:

```text
CURRENT_SOURCE_UNSUPPORTED_THEOREM_SHAPE
```

not mathematical falsity.

## 3. Frequency, normalization, exponent, and sharp constant

The literal additive-coordinate mode is

[
U_{n,m}(x)
==========

L_m^{-1/2}
\exp!\left(\frac{2\pi i n x}{L_m}\right).
]

Therefore its physical angular frequency is exactly

[
\boxed{
\omega_i(n)=\frac{2\pi n}{L_m(i)}.
}
]

The order-one coefficient energy is consequently

[
\boxed{
E_i(f)
======

\sum_{n\in\mathbb Z}
|\omega_i(n)|^2
\left|\left\langle V_{n,m},f\right\rangle\right|^2.
}
]

The exponent is (2), not (1), (4), or an unscaled (n^2). The length factor has already survived the Phase-4K Haar-versus-volume plant and literal-basis identification.  `[ABSTRACT][LEAN]`

Since

```lean
modeSet i = Finset.Icc (-(i.N : ℤ)) (i.N : ℤ),
```

the exact omitted-mode arithmetic is:

[
n\notin\operatorname{modeSet}(i)
\quad\Longrightarrow\quad
N_i+1\le |n|.
]

Define the physical retained bandwidth by

[
\boxed{
W_i
===

\frac{2\pi(N_i+1)}{L_m(i)}.
}
]

Then every omitted mode satisfies

[
W_i\le|\omega_i(n)|,
]

and hence

[
1
\le
W_i^{-2}|\omega_i(n)|^2.
]

The clean Lean factor is:

```lean
((physicalFourierBandwidth i)⁻¹) ^ 2
```

It is exactly equal to

[
\left(
\frac{L_m(i)}
{2\pi(N_i+1)}
\right)^2.
]

The `W⁻²` spelling is preferable in the production theorem because:

* positivity of `W` is proved once;
* reciprocal convergence follows directly from `W → atTop`;
* no duplicate division convention appears;
* the first omitted mode (n=\pm(N+1)) gives equality.

`N+1` is load-bearing. It is not cosmetic sharpening.

## 4. Candidate comparison

| Candidate                                                                             | Source truth              |                                                          Wall reduction |          Public cost | Hidden analytic work                                               | Verdict                               |
| ------------------------------------------------------------------------------------- | ------------------------- | ----------------------------------------------------------------------: | -------------------: | ------------------------------------------------------------------ | ------------------------------------- |
| **A. Fixed physical inequality + independent bounded-energy and bandwidth suppliers** | Exact                     |              Removes the actual edge into `SelectedProjectionTailDecay` |             Moderate | None hidden; both suppliers remain visible                         | **Selected, repaired**                |
| **B. Fixed-(i) inequality only**                                                      | Exact                     | Closes only local algebra, leaving an immediate filter-algebra boundary |                Small | None                                                               | Rejected as an artificial boundary    |
| **C. Unconditional theorem from current `ProlatePair` data**                          | Unsupported               |                                  Would pretend source regularity exists |    Potentially large | All source analysis hidden                                         | **Killed as current-interface route** |
| **D. Assume directly (W_k^{-2}E_k\to0)**                                              | Mathematically sufficient |                                       Gives a weaker sufficient premise |                Small | Collapses the two diagnostic suppliers into a near-target majorant | Retained as nonactive fallback        |
| **E. Reselect `parent`/`extract` after observing tail errors**                        | Changes the fixed family  |                                      Could manufacture a favorable path | Structural migration | Post-hoc schedule selection                                        | **Killed**                            |

### Candidate A

Candidate A is an honest receiver, not premise wrapping.

Its first theorem is an unconditional fixed-index consequence of Phase 4J and Phase 4K. Its second theorem is a pure filter-theoretic implication from two independently meaningful contracts:

```text
selected physical energy is summable at every k and bounded along the path;
selected physical bandwidth tends to infinity.
```

Neither premise mentions projection error, `SelectedProjectionTailDecay`, normalized residual decay, Mellin coordinates, `rawFplus`, `Gwin`, `SlotS2`, PX, or RH.

### Candidate B

Stopping after the fixed-(i) theorem would create another review boundary around a short multiplication-and-squeeze argument. No new object choice or analytic theorem occurs between the fixed estimate and the selected conditional receiver. Under `MINIMAL_LEMMA`, both belong in one transaction.

### Candidate C

The current source interface has no theorem identifying the full selected `E_star` object with a periodic logarithmic (H^1) function and no uniform weighted-energy estimate. Deriving one anyway would be a **C10 functional/surrogate failure**: the proof would apply regularity belonging to a reconstructed or wished-for object, not the literal source object.  `[COFINAL_FAMILY][PAPER]` **[C10]**

This kills Candidate C **from current data**. It does not refute the existence of a future source theorem.

### Candidate D

Candidate D is not logically false. In fact,

[
W_k^{-2}E_k\to0
]

is weaker than “(E_k) bounded and (W_k\to\infty).”

It is not selected because it obscures which independent mechanism is missing and comes close to naming the exact majorant required by the target. Candidate A keeps the schedule and source-energy obligations separately falsifiable. This is the relevant **C12 boundedness** discipline. **[C12]**

If a later source theorem yields unbounded energy but a usable coupled rate, Candidate D is the correct representation shift. Failure of Candidate A’s sufficient premises will not kill projection-tail decay.

### Candidate E

The selected path is already frozen as:

```lean
S.canonical.parent (S.canonical.extract k).
```

Reselecting it after observing projection errors is post-outcome witness choice, hence a **C09 precommit failure**. It also violates **C04** by replacing the exact family while preserving only coarse cofinal labels. **[C09][C04]**

The Arsenal deck and pending mandate were fetched and their standing attack-duals are applied here.

## 5. Selected production transaction

### Owned module

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarPhysicalFourierEnergyControl.lean
```

### Exact imports

```lean
import Q3.Proofs.RouteB.D0LogWindowVNMCompletenessBridge
import Q3.Proofs.RouteB.D0PstarGalerkinResidualDecay
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Normed.Ring.Lemmas
```

The two project imports are exact:

* Phase 4K supplies literal completeness and projection-complement Parseval;
* Phase 4H supplies the selected residual object and `SelectedProjectionTailDecay`.

The Mathlib imports supply reciprocal convergence at `atTop` and bounded-times-zero multiplication. The pinned APIs include:

```lean
Filter.Tendsto.inv_tendsto_atTop
Filter.isBoundedUnder_le_mul_tendsto_zero
```

with exactly the required directions.   `[ABSTRACT][LEAN]`

### Namespace

```lean
namespace Q3.RouteB.D0Pstar
```

## 6. Exact public declarations

### 6.1 Physical frequency

```lean
/-- Physical angular frequency of the literal log-window Fourier mode. -/
def physicalFourierFrequency
    (i : PairIndex) (n : ℤ) : ℝ :=
  (2 * Real.pi * (n : ℝ)) / L_m i
```

### 6.2 Physical weight

```lean
/-- Order-one physical Fourier weight. -/
def physicalFourierWeight
    (i : PairIndex) (n : ℤ) : ℝ :=
  |physicalFourierFrequency i n| ^ 2
```

### 6.3 Coefficient orientation

```lean
/-- Literal Phase-4D coefficient orientation: basis vector in the first slot. -/
def physicalFourierCoefficient
    (i : PairIndex) (f : H_m i) (n : ℤ) : ℂ :=
  inner ℂ (V_n_m i n) f
```

This public definition is intentional. The scalar energy does not distinguish `inner(V,f)` from `inner(f,V)` after taking a norm, so the orientation must be locked before that forgetful operation.

### 6.4 Fixed-index physical energy

```lean
/-- Physical order-one coefficient energy of a vector in the literal carrier. -/
noncomputable def physicalFourierEnergy
    (i : PairIndex) (f : H_m i) : ℝ :=
  ∑' n : ℤ,
    physicalFourierWeight i n *
      ‖physicalFourierCoefficient i f n‖ ^ 2
```

The definition does not assert summability. Summability remains an explicit hypothesis wherever the `tsum` is consumed.

### 6.5 Physical retained bandwidth

```lean
/-- First omitted physical angular frequency. -/
def physicalFourierBandwidth
    (i : PairIndex) : ℝ :=
  (2 * Real.pi * ((i.N + 1 : ℕ) : ℝ)) / L_m i
```

### 6.6 Selected full-object energy

```lean
/--
Physical energy of the literal full source object, on the existing
`parent ∘ extract` path.
-/
noncomputable def selectedPhysicalFourierEnergy
    (S : ProlateCanonicalSourceData) (k : ℕ) : ℝ :=
  let i := selectedPairIndex S k
  let h := selectedProlateTrial S k
  let hLp := S.source.eStar_memLp i
  physicalFourierEnergy i (gTrial_m i h hLp)
```

This must use `gTrial_m`, not `gTrial_m_N`. The latter is the projected object whose omitted coefficients vanish by construction. The source definitions distinguish the full object and its finite projection exactly.  `[ABSTRACT][LEAN]`

### 6.7 Selected energy control

```lean
/--
Independent selected-energy contract:
each physical coefficient row is summable, and the resulting energies
are eventually bounded.
-/
def SelectedPhysicalFourierEnergyControl
    (S : ProlateCanonicalSourceData) : Prop :=
  (∀ k : ℕ,
    let i := selectedPairIndex S k
    let h := selectedProlateTrial S k
    let hLp := S.source.eStar_memLp i
    Summable
      (fun n : ℤ =>
        physicalFourierWeight i n *
          ‖physicalFourierCoefficient
              i (gTrial_m i h hLp) n‖ ^ 2)) ∧
  IsBoundedUnder (· ≤ ·) atTop
    (norm ∘ selectedPhysicalFourierEnergy S)
```

This is a named `Prop`, not a field added to `ProlateCanonicalSourceData`.

The two conjuncts must remain separate. A bounded numerical value of `tsum` does not imply summability; in Lean, a nonsummable `tsum` can collapse to zero.

### 6.8 Selected bandwidth cofinality

```lean
/-- The first omitted physical frequency tends to infinity on the frozen path. -/
def SelectedPhysicalBandwidthCofinal
    (S : ProlateCanonicalSourceData) : Prop :=
  Tendsto
    (fun k : ℕ =>
      physicalFourierBandwidth (selectedPairIndex S k))
    atTop
    atTop
```

This is deliberately not inferred from `PairCofinal`.

## 7. Exact private helpers

Exactly three private theorems are permitted.

### 7.1 Positivity

```lean
private theorem physicalFourierBandwidth_pos
    (i : PairIndex) :
    0 < physicalFourierBandwidth i := by
  ...
```

### 7.2 Factor normalization

```lean
private theorem physicalFourierBandwidth_inv_sq_eq
    (i : PairIndex) :
    ((physicalFourierBandwidth i)⁻¹) ^ 2 =
      (L_m i /
        (2 * Real.pi * ((i.N + 1 : ℕ) : ℝ))) ^ 2 := by
  ...
```

### 7.3 Sharp omitted-mode guard

```lean
private theorem one_le_bandwidth_inv_sq_mul_physicalWeight_of_not_mem_modeSet
    (i : PairIndex) (n : ℤ)
    (hn : n ∉ modeSet i) :
    1 ≤
      ((physicalFourierBandwidth i)⁻¹) ^ 2 *
        physicalFourierWeight i n := by
  ...
```

This theorem must derive (N+1\le|n|) from the literal `Finset.Icc` membership failure. No looser postulated cutoff is permitted.

## 8. Public theorem 1 — fixed-index physical tail

```lean
/--
The exact finite Galerkin residual is controlled by the physical
order-one coefficient energy at the sharp first-omitted-mode scale.
-/
theorem norm_sub_coe_P_m_N_sq_le_bandwidth_inv_sq_mul_physicalFourierEnergy
    (i : PairIndex) (f : H_m i)
    (hsum :
      Summable
        (fun n : ℤ =>
          physicalFourierWeight i n *
            ‖physicalFourierCoefficient i f n‖ ^ 2)) :
    ‖f - (P_m_N i f : H_m i)‖ ^ 2 ≤
      ((physicalFourierBandwidth i)⁻¹) ^ 2 *
        physicalFourierEnergy i f := by
  ...
```

`[ABSTRACT][CONDITIONAL]`

After production validation: `[ABSTRACT][LEAN]`.

### Proof route

Instantiate the Phase-4J theorem with:

```text
basis    = V_n_m_hilbertBasis i
retained = modeSet i
a        = W_i⁻²
w n      = |ω_i(n)|².
```

The required hypotheses are:

* (0\le W_i^{-2});
* (0\le|\omega_i(n)|^2);
* the private omitted-mode guard;
* `hsum`.

Then rewrite:

```text
V_n_m_hilbertBasis i n = V_n_m i n
```

and the finite partial sum as the literal `P_m_N` projection using the closed Phase-4D/4K reconstruction.

No source regularity or selected-family assumption enters this theorem.

## 9. Public theorem 2 — selected conditional tail decay

```lean
/--
Bounded selected physical energies and diverging physical bandwidth imply
the already-defined literal selected projection-tail decay.
-/
theorem selectedProjectionTailDecay_of_physicalFourierEnergyControl
    (S : ProlateCanonicalSourceData)
    (hEnergy : SelectedPhysicalFourierEnergyControl S)
    (hBandwidth : SelectedPhysicalBandwidthCofinal S) :
    SelectedProjectionTailDecay S := by
  ...
```

`[COFINAL_FAMILY][CONDITIONAL]`

After production validation: `[COFINAL_FAMILY][LEAN]`, with both analytic suppliers still conditional.

### Exact filter proof

Let

[
W_k
===

\operatorname{physicalFourierBandwidth}
(\operatorname{selectedPairIndex}S,k),
\qquad
E_k
===

\operatorname{selectedPhysicalFourierEnergy}S,k.
]

1. `hBandwidth` gives (W_k\to+\infty).

2. Pinned Mathlib’s `Filter.Tendsto.inv_tendsto_atTop` gives:

   [
   W_k^{-1}\to0.
   ]

   Squaring gives:

   [
   W_k^{-2}\to0.
   ]

   `[ABSTRACT][LEAN]`

3. `hEnergy.2` supplies eventual boundedness of (E_k). Apply:

   ```lean
   Filter.isBoundedUnder_le_mul_tendsto_zero
   ```

   to obtain:

   [
   E_kW_k^{-2}\to0.
   ]

   Commutativity rewrites this as (W_k^{-2}E_k\to0).  `[ABSTRACT][LEAN]`

4. For each (k), apply the fixed-index theorem to the **full** object:

   ```lean
   gTrial_m i h hLp
   ```

   using `hEnergy.1 k` for summability.

5. Rewrite:

   ```lean
   gTrial_m_N i h hLp = P_m_N i (gTrial_m i h hLp)
   ```

   and use symmetry of the norm under subtraction reversal.

6. This gives:

   [
   \bigl(
   \operatorname{selectedUnnormalizedGalerkinResidualNorm}S,k
   \bigr)^2
   \le
   W_k^{-2}E_k.
   ]

7. Use `tendsto_order` directly. For every (b>0), eventually the majorant is below (b^2). Since the residual norm is nonnegative, the square inequality implies that the residual norm is below (b).

This avoids any hidden use of square-root continuity, any normalizer bound, and any claim that bandwidth or energy is automatically positive “eventually” without proof.

## 10. K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  carrier:
    fixed: H_m i
    selected: H_m (selectedPairIndex S k)

  full_source_object:
    gTrial_m
      (selectedPairIndex S k)
      (selectedProlateTrial S k)
      (S.source.eStar_memLp ...)

  projected_object:
    gTrial_m_N
    role: residual endpoint only
    forbidden_as_energy_source: true

  basis:
    literal V_n_m_hilbertBasis

  coefficient:
    inner Complex (V_n_m i n) f

  physical_frequency:
    2*pi*n/L_m

  physical_weight:
    abs(2*pi*n/L_m)^2

  retained_modes:
    exact modeSet = Icc (-N) N

  first_omitted_index:
    N_plus_1

  bandwidth:
    2*pi*(N+1)/L_m

  factor:
    bandwidth_inverse_squared

  selected_path:
    canonical.parent (canonical.extract k)

  source_energy_contract:
    per_k_summable_AND_eventually_bounded

  schedule_contract:
    bandwidth_tendsto_atTop

  forbidden:
    - infer_bandwidth_from_PairCofinal
    - use_projected_object_energy
    - assume_projection_tail
    - reselect_parent_or_extract
    - bare_n_squared_weight
```

## 11. Mandatory semantic plants

### `P056U-1 — summability`

Mutation: remove the per-(k) `Summable` premise.

Control: a nonnegative nonsummable series whose Lean `tsum` is zero. The mutated theorem would allow a positive omitted residual to be bounded by zero.

Expected failure:

```text
G6_S2_PHYSICAL_FOURIER_NONSUMMABLE_TSUM_ZERO
```

### `P056U-2 — physical scaling`

Mutation:

```text
physicalFourierWeight i n
→ (n : ℝ)^2.
```

Control: verify the exact derivative-frequency law

[
\omega_i(n)L_m(i)=2\pi n
]

at two different log-window lengths. Bare (n^2) forgets the changing physical scale.

Expected failure:

```text
G6_S2_PHYSICAL_FOURIER_FREQUENCY_NORMALIZATION_MISMATCH
```

### `P056U-3 — \(N+1\), not \(N\)`

Mutation:

```text
2*pi*(N+1)/L
→ 2*pi*N/L.
```

Control: take (N=0) and (f=V_{1,m}). The literal projection is zero, the residual norm squared is one, and the correct first omitted bandwidth is positive. The mutated bandwidth is zero, whose Lean inverse is zero, producing a false zero right-hand side.

Expected failure:

```text
G6_S2_PHYSICAL_FOURIER_MODESET_GUARD_MISMATCH
```

### `P056U-4 — coefficient orientation`

Mutation:

```text
inner ℂ (V_n_m i n) f
→ inner ℂ f (V_n_m i n).
```

Control:

[
f=i,V_{n,m}.
]

Then:

[
\langle V_n,iV_n\rangle=i,
\qquad
\langle iV_n,V_n\rangle=-i.
]

The energy norm alone cannot see this mutation; the public coefficient definition and its dedicated plant must.

Expected failure:

```text
G6_S2_PHYSICAL_FOURIER_INNER_ORIENTATION_MISMATCH
```

### `P056U-5 — `PairCofinal` is not physical cofinality`

Mutation: derive `SelectedPhysicalBandwidthCofinal` from `parentCofinal`.

Control:

[
m_k=2^{(k+1)^2},
\qquad
N_k=k+1.
]

Both coordinates diverge, while physical bandwidth tends to zero.

Expected failure:

```text
G6_S2_PHYSICAL_BANDWIDTH_PAIRCOFINAL_SMUGGLE
```

### `P056U-6 — selected path identity`

Mutation:

```text
selectedPairIndex S k
→ (S.canonical.parent k).1
```

or shift `extract`.

Expected failure:

```text
G6_S2_PHYSICAL_FOURIER_SELECTED_PATH_MISMATCH
```

### `P056U-7 — bounded energy is load-bearing for Candidate A`

Mutation: remove eventual boundedness while retaining bandwidth divergence.

Control:

[
W_k=k+1,
\qquad
E_k=(k+1)^2.
]

Then (W_k^{-2}E_k=1), so the majorant does not tend to zero.

Expected failure:

```text
G6_S2_PHYSICAL_FOURIER_ENERGY_BOUNDEDNESS_MISSING
```

This is the active **C12** plant.

### `P056U-8 — full versus projected object`

Mutation: define selected energy from `gTrial_m_N`.

Control: take a full object with a nonzero first omitted basis mode. Its projected object has zero omitted coefficients, making the mutated energy zero while the full projection residual is nonzero.

Expected failure:

```text
G6_S2_PHYSICAL_FOURIER_PROJECTED_OBJECT_SURROGATE
```

This is the active **C10** plant.

### `P056U-9 — no tail restatement`

Mutation: insert `SelectedProjectionTailDecay S` as a hypothesis or into either new supplier definition.

Expected failure:

```text
G6_S2_PHYSICAL_RECEIVER_TAIL_RESTATEMENT
```

The scan must permit `SelectedProjectionTailDecay` only as the conclusion of the public receiver, never as an input.

## 12. Validation gates

### Source lock

Before editing:

```text
HEAD = origin/rh_clean =
6f28c1cf2668628dfb61f0d7b2daa2eb5d6a7277
```

Verify all seven required SHA-256 values.

### Lean

```bash
lake env lean \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarPhysicalFourierEnergyControl.lean

lake build Q3.Proofs.RouteB.D0PstarPhysicalFourierEnergyControl

lake build

bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarPhysicalFourierEnergyControl.lean
```

Report actual target/full job counts; do not predeclare a pass count.

### Taint and imports

Require zero:

```text
sorry
admit
exact?
native_decide
declared axiom
opaque certificate
Float
aristotle_output import
ACTIVE/RequestProject import
Q3.Main edit
source-structure mutation
```

### Public surface

Require exactly:

```text
8 public definitions
2 public theorems
3 private theorems
0 private definitions
13 total declarations
```

No generated structure fields are allowed because both supplier contracts are plain `Prop` definitions.

### Axiom audit

```lean
#print axioms
  Q3.RouteB.D0Pstar.norm_sub_coe_P_m_N_sq_le_bandwidth_inv_sq_mul_physicalFourierEnergy

#print axioms
  Q3.RouteB.D0Pstar.selectedProjectionTailDecay_of_physicalFourierEnergyControl
```

Each must return exactly:

```text
[propext, Classical.choice, Quot.sound]
```

### Plants and infrastructure

Require:

```text
P056U-1 through P056U-9 all FIRED
temporary plant files removed

proof DB:
  13 declarations indexed
  5 theorem declarations proven

orchestrator:
  67/67 tests PASS

Spine:
  python3 orchestrator/spine.py --strict --reason goal-close
  strict PASS

observability:
  8 sources
  0 stale
  numeric ZERO_COVERAGE reported separately, never as PASS

SQLite:
  knowledge.db = ok
  aristotle_proofs.db = ok
  observability.db = ok

git diff --check
exact git status report
```

## 13. What this transaction proves

On success:

[
\boxed{
\text{fixed physical coefficient energy}
\Longrightarrow
\text{sharp fixed-index projection-tail bound}.
}
]

`[ABSTRACT][LEAN]`

And:

[
\boxed{
\text{summable bounded selected energies}
+
\text{physical bandwidth}\to\infty
\Longrightarrow
\texttt{SelectedProjectionTailDecay}.
}
]

`[COFINAL_FAMILY][LEAN]`

It will **not** prove:

```text
the selected physical energy is summable;
the selected energies are bounded;
physical bandwidth tends to infinity;
selected normalizers are bounded;
normalized residual decay unconditionally;
compact-open residual decay;
strict SlotS2;
route promotion;
PX;
RH.
```

Those remain `[COFINAL_FAMILY][CONDITIONAL]`.

## 14. Direct consumer and sole next node

The direct downstream consumer already exists:

```lean
selectedNormalizedGalerkinResidual_norm_tendsto_zero_of_tail_and_bounded
```

It consumes:

```lean
selectedProjectionTailDecay_of_physicalFourierEnergyControl
```

as its `hTail` argument and still requires the independent
`SelectedTrialNormalizerBounded` supplier. This preserves the Phase-4H factorization rather than silently merging the two analytic walls.  `[COFINAL_FAMILY][LEAN]`

The sole next node, not authorized in this batch, is:

```text
G6_S2_D0_SELECTED_PROLATE_PHYSICAL_FOURIER_ENERGY_SOURCE_SUPPLIER
```

Its target must be a source-grounded logarithmic-coordinate regularity theorem—periodic weak derivative, Sobolev estimate, or an equivalent coefficient-energy theorem—proving `SelectedPhysicalFourierEnergyControl S` for the literal full `gTrial_m` family.

The physical-bandwidth premise remains separately open. It is not the selected next node and may not be obtained by reselection of the frozen path.

## STRONGEST ATTACK

> Candidate A assumes bounded energy and bandwidth divergence. These are stronger than necessary. If either fails, has the route been killed?

No.

Candidate A is a sufficient factorized route. It is not an equivalence. A selected family may have unbounded energy while still satisfying

[
W_k^{-2}E_k\to0.
]

In that case Candidate D becomes the correct repaired representation.

Therefore the legal failure interpretation is:

```text
A_SUPPLIER_FAILED
```

not:

```text
SELECTED_PROJECTION_TAIL_DECAY_FALSE
```

and not:

```text
ROUTE_B_KILLED.
```

The second attack is more serious:

> Why should the logarithmic representative of `E_star(prolateCombination)` have finite periodic order-one energy at all?

Current data does not answer that. The source object may have an endpoint seam or insufficient regularity. That is exactly why the next source supplier remains open and why Candidate C is rejected.

The receiver selected here is still valuable: it makes that question exact and testable without inserting it as a field, axiom, opaque certificate, or theorem premise named as if already proved.

## META CLOSEOUT

**What became smaller?**

The vague wall

```text
selected Fourier tail must vanish
```

is reduced to:

```text
fixed exact physical inequality;
per-k physical energy summability;
selected energy boundedness;
physical bandwidth divergence.
```

**What was killed?**

* unscaled (n^2) as the physical weight;
* `PairCofinal` as a bandwidth theorem;
* `N` in place of `N+1`;
* projected-vector energy as a surrogate for full-object energy;
* unconditional current-source energy control;
* post-hoc parent/extract reselection.

**What must not be tried again?**

Do not infer a source Sobolev theorem from mere `MemLp`. Do not infer a rate from independent cofinality. Do not hide nonsummability behind Lean’s `tsum`.

**Current smallest named gap:**

```text
G6_S2_D0_SELECTED_PHYSICAL_FOURIER_ENERGY_RECEIVER_MISSING
```

**Next cheapest decisive test:**

Compile the fixed-index theorem and fire the (N=0,\ f=V_1) cutoff plant before writing selected-path filter algebra.

**Fate of registered predictions:**

```text
Phase4K:
  completeness would expose, not solve, the physical-energy wall.
  CONFIRMED.

Phase4I:
  PairCofinal would not imply physical bandwidth.
  CONFIRMED.

Phase4L:
  current source data would not supply unconditional energy control.
  CONFIRMED BY TYPE AUDIT.

Candidate A:
  fixed inequality plus bounded-times-inverse-bandwidth glue is executable.
  SELECTED; production validation pending.
```

```yaml
iteration:
  target: selected_physical_Fourier_energy_control
  status: OPEN
  failed_strategy: infer_physical_tail_from_completeness_or_independent_cofinality
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: G6_S2_D0_SELECTED_PHYSICAL_FOURIER_ENERGY_RECEIVER_MISSING
  invariant_learned: physical_scale_summability_bounded_energy_and_frozen_schedule_are_independent
  forbidden_future_move: use_projected_energy_or_reselect_parent_extract
  next_decisive_test: fixed_index_physical_tail_compile_plus_N_zero_first_omitted_mode_plant
  progress_class: PROOF_PROGRESS
  route_score: 5
```

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS:
  TRY_G6_S2_D0_SELECTED_PHYSICAL_FOURIER_ENERGY_RECEIVER

TRANSACTION:
  G6_S2_D0_SELECTED_PHYSICAL_FOURIER_ENERGY_RECEIVER

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

PHASE:
  phase_key_change: false
  reuse_conversation_id: 6a72e750-dc60-83eb-946b-61d2073c232b
  fresh_chat: forbidden

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: 6f28c1cf2668628dfb61f0d7b2daa2eb5d6a7277

  required_sha256:
    q3.lean.aristotle/Q3/Proofs/RouteB/D0LogWindowVNMCompletenessBridge.lean:
      1001bd3c39dcf70ae4d7c31bbc8c0f188d1f9917331b22bb5b0f981cc832e949
    q3.lean.aristotle/Q3/Proofs/RouteB/D0HilbertBasisWeightedTail.lean:
      24956f668098ea0a940ba50ebdd4087d7645114c8c0919a5587f35f10135643c
    q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarGalerkinResidualDecay.lean:
      8fe089afef9e6a43f7b6c7b7b737bc0709e7e35d41ae73a34ab94c49f1f62f63
    q3.lean.aristotle/Q3/Proofs/RouteB/D0ProlateKTrialSource.lean:
      7597910a8cf2160c4ab9786144d25595a6c519395f64fc0846d84a249a96c016
    q3.lean.aristotle/Q3/Proofs/RouteB/D0CanonicalApproximation.lean:
      60409208d26aeae7b4974150bd66ad42da83f09a223f41196dbde7abd3157695
    q3.lean.aristotle/docs/INSIGHTS.md:
      11dfef606e5310b9ce503f389f47f45003df62a052f68c344a0fb612da31adb0
    q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_STATE.md:
      e75457bf7c5e78284e6e434dc94d9e98cc9f870adfc24ce560dfe5374e87aa66

ON_SOURCE_MISMATCH:
  stop: G6_S2_PHYSICAL_FOURIER_SOURCE_LOCK_MISMATCH
  edit_files: false

CREATE:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarPhysicalFourierEnergyControl.lean

IMPORTS_EXACT:
  - Q3.Proofs.RouteB.D0LogWindowVNMCompletenessBridge
  - Q3.Proofs.RouteB.D0PstarGalerkinResidualDecay
  - Mathlib.Topology.Algebra.Order.Field
  - Mathlib.Analysis.Normed.Ring.Lemmas

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE:
  definitions: 8
  theorems: 2
  private_theorems: 3
  private_definitions: 0
  total_declarations: 13

PUBLIC_DEFINITIONS:
  - physicalFourierFrequency
  - physicalFourierWeight
  - physicalFourierCoefficient
  - physicalFourierEnergy
  - physicalFourierBandwidth
  - selectedPhysicalFourierEnergy
  - SelectedPhysicalFourierEnergyControl
  - SelectedPhysicalBandwidthCofinal

PRIVATE_THEOREMS:
  - physicalFourierBandwidth_pos
  - physicalFourierBandwidth_inv_sq_eq
  - one_le_bandwidth_inv_sq_mul_physicalWeight_of_not_mem_modeSet

PUBLIC_THEOREM_1: |
  theorem norm_sub_coe_P_m_N_sq_le_bandwidth_inv_sq_mul_physicalFourierEnergy
      (i : PairIndex) (f : H_m i)
      (hsum :
        Summable
          (fun n : ℤ =>
            physicalFourierWeight i n *
              ‖physicalFourierCoefficient i f n‖ ^ 2)) :
      ‖f - (P_m_N i f : H_m i)‖ ^ 2 ≤
        ((physicalFourierBandwidth i)⁻¹) ^ 2 *
          physicalFourierEnergy i f := by
    ...

PUBLIC_THEOREM_2: |
  theorem selectedProjectionTailDecay_of_physicalFourierEnergyControl
      (S : ProlateCanonicalSourceData)
      (hEnergy : SelectedPhysicalFourierEnergyControl S)
      (hBandwidth : SelectedPhysicalBandwidthCofinal S) :
      SelectedProjectionTailDecay S := by
    ...

REQUIRED_PROOF_ROUTE:
  fixed_index:
    - instantiate norm_sub_basisPartialSum_sq_le_weightedEnergy
    - use literal V_n_m_hilbertBasis
    - use exact modeSet
    - use a = physicalFourierBandwidth_inverse_squared
    - use w = physicalFourierWeight
    - prove N_plus_1_le_abs_n outside modeSet
    - rewrite finite sum to P_m_N
    - retain explicit Summable hypothesis

  selected_path:
    - use exactly selectedPairIndex S k
    - use exactly selectedProlateTrial S k
    - compute energy on full gTrial_m
    - use hEnergy first conjunct for each fixed theorem
    - derive inverse_bandwidth_squared_tendsto_zero from hBandwidth
    - combine bounded energy with inverse bandwidth using
      Filter.isBoundedUnder_le_mul_tendsto_zero
    - use squared pointwise inequality and tendsto_order
    - conclude the existing SelectedProjectionTailDecay definition

FORBIDDEN:
  - add fields to ProlateCanonicalSourceData
  - infer physical bandwidth from PairCofinal
  - use bare n_squared weight
  - use N instead of N_plus_1
  - compute selected energy from gTrial_m_N
  - reverse coefficient orientation
  - omit per_k Summable
  - hide summability behind a finite tsum value
  - assume SelectedProjectionTailDecay
  - assume normalized residual decay
  - reselect parent or extract
  - add periodic_H1 or Sobolev source facts without proof
  - modify Phase4H, Phase4I, Phase4J, or Phase4K files
  - edit Q3.Main
  - edit Goal_055
  - create Bus_010
  - submit Aristotle
  - promote Route_B
  - make PX_or_RH_claim
  - open a fresh Proshka chat

MANDATORY_PLANTS:
  P056U_1_SUMMABILITY:
    expected: G6_S2_PHYSICAL_FOURIER_NONSUMMABLE_TSUM_ZERO

  P056U_2_PHYSICAL_SCALING:
    expected: G6_S2_PHYSICAL_FOURIER_FREQUENCY_NORMALIZATION_MISMATCH

  P056U_3_N_PLUS_ONE:
    control: N_zero_and_first_omitted_mode_V_one
    expected: G6_S2_PHYSICAL_FOURIER_MODESET_GUARD_MISMATCH

  P056U_4_INNER_ORIENTATION:
    control: f_equals_I_smul_V_n
    expected: G6_S2_PHYSICAL_FOURIER_INNER_ORIENTATION_MISMATCH

  P056U_5_PAIRCOFINAL:
    control: m_k_eq_2_pow_k_plus_1_sq__N_k_eq_k_plus_1
    expected: G6_S2_PHYSICAL_BANDWIDTH_PAIRCOFINAL_SMUGGLE

  P056U_6_SELECTED_PATH:
    expected: G6_S2_PHYSICAL_FOURIER_SELECTED_PATH_MISMATCH

  P056U_7_ENERGY_BOUNDEDNESS:
    control: W_k_eq_k_plus_1__E_k_eq_k_plus_1_squared
    expected: G6_S2_PHYSICAL_FOURIER_ENERGY_BOUNDEDNESS_MISSING

  P056U_8_FULL_OBJECT:
    control: first_omitted_basis_mode
    expected: G6_S2_PHYSICAL_FOURIER_PROJECTED_OBJECT_SURROGATE

  P056U_9_NO_TAIL_RESTATEMENT:
    expected: G6_S2_PHYSICAL_RECEIVER_TAIL_RESTATEMENT

VALIDATION:
  - verify HEAD equals origin before editing
  - verify all seven SHA-256 locks
  - direct Lean on D0PstarPhysicalFourierEnergyControl.lean
  - dedicated module build
  - full build
  - q3_check PASS
  - hole taint and forbidden-import scan
  - exact public surface 8_definitions_2_theorems_3_private_theorems
  - fire P056U_1 through P056U_9
  - remove all temporary plant files
  - print axioms for both public theorems
  - require exactly [propext, Classical.choice, Quot.sound]
  - proof database reimport
  - require 13 declarations indexed
  - require 5 theorem declarations proven
  - run all 67 orchestration tests
  - run python3 orchestrator/spine.py --strict --reason goal-close
  - require strict Spine PASS
  - report observability 8_sources_0_stale
  - report numeric ZERO_COVERAGE separately
  - run SQLite integrity_check on knowledge.db
  - run SQLite integrity_check on aristotle_proofs.db
  - run SQLite integrity_check on observability.db
  - require all three results equal ok
  - git diff --check
  - exact git status report

STOP:
  G6_S2_D0_SELECTED_PHYSICAL_FOURIER_ENERGY_RECEIVER_MISSING

SUCCESS:
  G6_S2_D0_PHYSICAL_FOURIER_ENERGY_AND_BANDWIDTH_TO_PROJECTION_TAIL_PROVED

FAILURE_CODES:
  - G6_S2_PHYSICAL_FOURIER_SOURCE_LOCK_MISMATCH
  - G6_S2_PHYSICAL_FOURIER_FREQUENCY_NORMALIZATION_MISMATCH
  - G6_S2_PHYSICAL_FOURIER_MODESET_GUARD_MISMATCH
  - G6_S2_PHYSICAL_FOURIER_NONSUMMABLE_TSUM_ZERO
  - G6_S2_PHYSICAL_BANDWIDTH_PAIRCOFINAL_SMUGGLE
  - G6_S2_PHYSICAL_FOURIER_SELECTED_PATH_MISMATCH
  - G6_S2_PHYSICAL_FOURIER_INNER_ORIENTATION_MISMATCH
  - G6_S2_PHYSICAL_FOURIER_ENERGY_BOUNDEDNESS_MISSING
  - G6_S2_PHYSICAL_FOURIER_PROJECTED_OBJECT_SURROGATE
  - G6_S2_PHYSICAL_RECEIVER_TAIL_RESTATEMENT
  - G6_S2_PHYSICAL_RECEIVER_PUBLIC_SURFACE_MISMATCH
  - G6_S2_PHYSICAL_RECEIVER_PLANT_INERT
  - LEAN_BUILD_FAIL

AFTER_SUCCESS:
  fixed_index_physical_tail_bound: PROVED
  selected_projection_tail_decay:
    status: PROVED_CONDITIONALLY
    premises:
      - SelectedPhysicalFourierEnergyControl
      - SelectedPhysicalBandwidthCofinal
  source_energy_supplier: OPEN
  bandwidth_supplier: OPEN
  normalizer_boundedness: OPEN
  normalized_residual_decay_unconditional: OPEN
  compact_open_decay: OPEN
  SlotS2: OPEN

DIRECT_DOWNSTREAM_CONSUMER:
  Q3.RouteB.D0Pstar.selectedNormalizedGalerkinResidual_norm_tendsto_zero_of_tail_and_bounded

SOLE_NEXT_NODE_NOT_AUTHORIZED:
  name: G6_S2_D0_SELECTED_PROLATE_PHYSICAL_FOURIER_ENERGY_SOURCE_SUPPLIER
  target: >-
    prove per-k summability and selected bounded physical Fourier energy
    for the literal full gTrial_m source family from a source-grounded
    logarithmic-coordinate regularity theorem

ARISTOTLE:
  status: FORBIDDEN

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  bus_010: VOID
  goal_055: HOLD
  Aristotle_submission: NONE
  route_promotion: false
  PX_RH_CLAIM: NOT_MADE
```
