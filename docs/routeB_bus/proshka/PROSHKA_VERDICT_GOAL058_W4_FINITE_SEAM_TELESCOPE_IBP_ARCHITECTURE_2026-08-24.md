# STATUS: CONDITIONAL — TRY_W4_RIGHT_CONTINUOUS_CELL_TELESCOPE_IBP
```yaml
PRIMARY: TRY_W4_RIGHT_CONTINUOUS_CELL_TELESCOPE_IBP
OPERATIVE_CLASS: TRY_W4_RIGHT_CONTINUOUS_CELL_TELESCOPE_IBP
PRIMARY_COUNT: 1
DOCUMENT_ROLE: INDEPENDENT_OPERATIVE_PROOF_ARCHITECTURE_VERDICT

SOURCE_LOCK:
  REQUESTED_REPO_ALIAS: emalam/chen_q3
  CONNECTED_REPO: Malaeu/chen_q3
  ALIAS_RESOLUTION: REQUESTED_REPO_NOT_FOUND_EXACT_COMMIT_FOUND_IN_CONNECTED_REPO
  BRANCH: rh_clean
  REQUESTED_SOURCE_PIN: 92e03a6675ff52722b274ca0f3903b5f270d6629
  REQUESTED_SOURCE_FILE_BLOB: b2417ca0c5a72d6c163a93f1ca3ce43ecd0a47de
  EXECUTION_HEAD_AUDITED: 45bcbd31115a0d8648fe220548da429f83de7560
  EXECUTION_FILE_BLOB: 7fa4f84ff54be3da4aaa44d8af912e9c6d2f4bdb
  DELTA_FROM_REQUESTED_PIN:
    commit_count: 4
    source_only_additions: 202
    public_surface_changed: false
    added_private_suppliers:
      - selectedFerrersLemma73SourcePacket_hasDerivAt_of_mem_Ioo
      - selectedFerrersAbelLogArgument_hasDerivAt
      - selectedFerrersAbelLogPacketTerm_hasDerivAt_of_argument_mem_Ioo
      - selectedFerrersAbelLogProductionTerm
      - selectedFerrersAbelLogSqrtWeight_hasDerivAt
      - selectedFerrersAbelLogProductionTerm_hasDerivAt_of_argument_mem_Ioo
      - selectedFerrersAbelLogRepresentative_eq_productionSum
      - selectedFerrersAbelLogPacketTerm_absolutelyContinuousOnInterval_of_mapsToWindow
      - selectedFerrersAbelLogSqrtWeight_absolutelyContinuousOnInterval
      - selectedFerrersAbelLogProductionTerm_absolutelyContinuousOnInterval_of_mapsToWindow

MATHLIB_LOCK:
  REPOSITORY: leanprover-community/mathlib4
  COMMIT: 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
  INPUT_REV: v4.26.0
  REQUIRED_NEW_DIRECT_IMPORT:
    Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

KERNEL_RECEIPT:
  OWNER_REPORTED_AC_PREFIX_KERNEL_AND_SPINE_GREEN: true
  JUDGE_RERAN_KERNEL: false
  ADMITTED_SCOPE:
    - selectedFerrersLemma73SourcePacket_absolutelyContinuousOnInterval
    - selectedFerrersAbelLogRepresentative_absolutelyContinuousOnInterval_of_seamFree
    - selectedFerrersAbelLogRepresentative_intervalIntegrable_deriv_of_seamFree
  FOURIER_DECAY_KERNEL_STATUS: OPEN

ADJUDICATION:
  finite_jump_fourier_decay_statement_refuted: false
  selected_architecture: RIGHT_CONTINUOUS_FIXED_ACTIVE_CELL_PARTITION
  exact_cell_count: k_plus_1
  cell_active_set: ONE_THROUGH_N
  seam_coordinate: log_of_k_plus_2_over_n
  lower_endpoint_seam: n_eq_k_plus_2
  upper_endpoint_seam: n_eq_1_paid_by_upper_zero_extension_boundary
  internal_seams: n_in_2_through_k_plus_1
  integration_by_parts: PINNED_MATHLIB_RIGHT_DERIVATIVE_THEOREM
  telescope_before_norm: required
  sharp_lower_boundary: selectedFerrersAbelLogLowerRightValue
  safe_public_payment: FULL_VALUE_PLUS_EXACT_LAST_SUMMAND
  epsilon_trim_limit_route: rejected
  direct_seam_free_AC_on_closed_cells: rejected_as_false_hypothesis
  midpoint_surrogate: forbidden
  global_fourier_derivative_engine: forbidden

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
  ADDITIONAL_PUBLIC_DECLARATIONS: forbidden
  STATEMENT_WEAKENING: forbidden

CLOSES:
  - W4_FINITE_SEAM_PARTITION_THEOREM_SHAPE
  - W4_PINNED_IBP_ENGINE_SELECTION
  - W4_TELESCOPE_ORIENTATION
  - W4_N_EQ_K_PLUS_2_PAYMENT_ARCHITECTURE
OPENS:
  - W4_FINITE_SEAM_TELESCOPE_IBP_LEAN
NEXT_LOAD_BEARING_GAP: W4_FINITE_SEAM_TELESCOPE_IBP_LEAN

EXPECTED_AXIOM_PROFILE:
  - propext
  - Classical.choice
  - Quot.sound

SCOPE: ABSTRACT
VERIFIER: CONDITIONAL
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: BOUNDARY_CASE
ROUTE_SCORE: 5

ARSENAL_MANDATE:
  ACCEPTED: true
  SIDECAR_EXECUTION_TRIGGERED: false
ARSENAL_CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C13_RESTORE_SYMMETRY_BY_EXPLICIT_SHADOW

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
SHIFTED_FORM_DOMAIN: NOT_AUTHORIZED
W5_COFINAL_RATE: OUTSIDE_TRANSACTION
DOWNSTREAM_GOAL058_ASSEMBLY: OUTSIDE_TRANSACTION
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

| Item | Verdict | Exact boundary | Tags |
|---|---|---|---|
| AC prefix | **SURVIVES** | The first three frozen public theorems are present. Owner reports kernel and Spine green; judge did not rerun Lean. | `[ABSTRACT][CONDITIONAL]` |
| Exact closed cells | **SELECTED** | Use fixed active index sets and right-continuous lower endpoint values. Do not call the seam-free theorem on seam endpoints. | `[ABSTRACT][PAPER]` |
| Per-cell IBP | **EXECUTABLE SHAPE** | Pinned Mathlib provides the required complex-valued right-derivative integration-by-parts theorem. | `[ABSTRACT][LEAN]` |
| Finite telescope | **EXECUTABLE SHAPE** | There are exactly `k+1` cells, internal seams `2..k+1`, lower seam `k+2`, and upper boundary `1`. | `[ABSTRACT][PAPER]` |
| Public off-zero decay | **OPEN UNTIL KERNEL** | First prove the sharp lower-right estimate, then dominate it by the repaired public jump budget. | `[ABSTRACT][CONDITIONAL]` |
| Global fixed-`k` decay | **OPEN UNTIL KERNEL** | Combine the off-zero estimate with one exact `L¹` Fourier bound near `t=0`. | `[ABSTRACT][CONDITIONAL]` |
| Shifted form-domain assembly | **FORBIDDEN NOW** | Starts only after independent semantic admission of the completed W4 node. | `[ABSTRACT][CONDITIONAL]` |

## 1. SOURCE ADJUDICATION

The requested pin materializes the AC prefix and the repaired public jump budget, but not the two Fourier-decay theorems. The current branch advanced by four additive source commits while this review was running. Those commits add exactly the private packet derivative, log-chain derivative, production-term, production-sum, and closed-window AC suppliers needed below. They do not change a public declaration. `[ABSTRACT][LEAN]`

The remaining blocker is therefore no longer packet differentiability or closed-window packet AC. It is the exact finite partition, endpoint bookkeeping, interval-integral telescope, and conversion from the sharp lower-right boundary to the public safe ledger. `[ABSTRACT][PAPER]`

The route is not killed. For fixed `k`, the production comb is finite, its active set is constant between consecutive seams, every selected cell has an exact continuous representative, and the pinned library contains the required complex integration-by-parts theorem. `[ABSTRACT][PAPER]`

## 2. DECISIVE API FINDING

The existing theorem

```lean
selectedFerrersAbelLogRepresentative_absolutelyContinuousOnInterval_of_seamFree
```

cannot be applied to an exact closed partition cell. Every cell endpoint is itself a production seam. In particular, `x=0` and `n=k+2` satisfy the forbidden equality. Any proof that instantiates `selectedFerrersAbelLogSeamFreeOn` on a closed cell is proving a false hypothesis. `[ABSTRACT][LEAN]`

The repair is not an `ε`-trimmed interval followed by a limit. That route introduces a new one-sided-limit theorem, a limit through interval integrals, and a dominated-convergence layer merely to recover values already available by finite algebra. `[ABSTRACT][PAPER]`

The selected object is a private closed-cell representative with a fixed active set. It agrees with the production representative on the cell interior, agrees with the production full value at the upper endpoint, and equals the production full value minus the single entering seam at the lower endpoint. `[ABSTRACT][PAPER]`

## 3. EXACT SEAM GEOMETRY

Set

\[
M_k=k+2,
\qquad
\lambda_k=\sqrt{M_k},
\qquad
L_k=\log M_k,
\]

and define

\[
s_{k,n}=\log\frac{M_k}{n},
\qquad 1\le n\le M_k.
\]

Then

\[
s_{k,M_k}=0,
\qquad
s_{k,1}=L_k,
\qquad
s_{k,n+1}<s_{k,n}.
\]

On the open cell

\[
(s_{k,n+1},s_{k,n}),
\qquad 1\le n\le k+1,
\]

exactly the positive indices `1..n` are active. At `s_{k,n}`, the index `n` is retained at the full endpoint. At `s_{k,n+1}`, the full production representative additionally retains index `n+1`, while the right-hand cell representative excludes it. `[ABSTRACT][PAPER]`

The exact seam term is

\[
J_{k,n}
=
\sqrt{\frac{\lambda_k}{n}}\,
 h_k(\lambda_k),
\qquad
h_k=\operatorname{selectedFerrersLemma73SourcePacket}(k).
\]

The lower endpoint term is `J_{k,k+2}` and is already represented by

```lean
selectedFerrersAbelLogLowerEndpointSeam
```

and

```lean
selectedFerrersAbelLogLowerEndpointSeam_eq_lastSummand.
```

`[ABSTRACT][LEAN]`

### Frozen private definitions

```lean
private noncomputable def selectedFerrersAbelLogSeamPoint
    (k n : ℕ) : ℝ :=
  Real.log ((((k + 2 : ℕ) : ℝ)) / (n : ℝ))

private def selectedFerrersAbelLogActiveIndices
    (k n : ℕ) : Finset ℕ+ :=
  (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k)).filter
    (fun q : ℕ+ => (q : ℕ) ≤ n)

private noncomputable def selectedFerrersAbelLogSeamTerm
    (k n : ℕ) : ℂ :=
  (((Real.sqrt
      (lambda_m (selectedFerrersPreAnchorIndex k) / (n : ℝ)) : ℝ) : ℂ) *
    selectedFerrersLemma73SourcePacket k
      (lambda_m (selectedFerrersPreAnchorIndex k)))

private noncomputable def selectedFerrersAbelLogCell
    (k n : ℕ) (x : ℝ) : ℂ :=
  (∑ q ∈ selectedFerrersAbelLogActiveIndices k n,
      selectedFerrersAbelLogProductionTerm k q x) +
    (1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0 *
      (Real.sqrt
        (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) : ℂ)

private noncomputable def selectedFerrersAbelLogPartitionPoint
    (k j : ℕ) : ℝ :=
  selectedFerrersAbelLogSeamPoint k (k + 2 - j)
```

Equivalent definitional normal forms are allowed only if all theorem heads below remain exact and the SOURCE RECORD gives the equivalence. `[ABSTRACT][CONDITIONAL]`

### Frozen seam lemmas

```lean
private theorem selectedFerrersAbelLogSeamPoint_exp
    (k n : ℕ) (hn : 0 < n) :
    Real.exp (selectedFerrersAbelLogSeamPoint k n) =
      ((k + 2 : ℕ) : ℝ) / (n : ℝ)

private theorem selectedFerrersAbelLogSeamPoint_last
    (k : ℕ) :
    selectedFerrersAbelLogSeamPoint k (k + 2) = 0

private theorem selectedFerrersAbelLogSeamPoint_one
    (k : ℕ) :
    selectedFerrersAbelLogSeamPoint k 1 =
      L_m (selectedFerrersPreAnchorIndex k)

private theorem selectedFerrersAbelLogSeamPoint_succ_lt
    (k n : ℕ) (hn : 1 ≤ n) (hnk : n ≤ k + 1) :
    selectedFerrersAbelLogSeamPoint k (n + 1) <
      selectedFerrersAbelLogSeamPoint k n

private theorem selectedFerrersAbelLogArgument_at_own_seam
    (k n : ℕ) (hn : 0 < n) :
    selectedFerrersAbelLogArgument k ⟨n, hn⟩
      (selectedFerrersAbelLogSeamPoint k n) =
        lambda_m (selectedFerrersPreAnchorIndex k)

private theorem selectedFerrersAbelLogPartitionPoint_zero
    (k : ℕ) :
    selectedFerrersAbelLogPartitionPoint k 0 = 0

private theorem selectedFerrersAbelLogPartitionPoint_last
    (k : ℕ) :
    selectedFerrersAbelLogPartitionPoint k (k + 1) =
      L_m (selectedFerrersPreAnchorIndex k)

private theorem selectedFerrersAbelLogPartitionPoint_strict
    (k j : ℕ) (hj : j < k + 1) :
    selectedFerrersAbelLogPartitionPoint k j <
      selectedFerrersAbelLogPartitionPoint k (j + 1)
```

These are exact arithmetic consequences of `lambda_k^2=k+2`. No numerical normalization is admissible. `[ABSTRACT][CONDITIONAL]`

## 4. CLOSED-CELL REPRESENTATIVE CONTRACT

For `1 ≤ n ≤ k+1`, prove the following exact statements.

```lean
private theorem selectedFerrersAbelLogCell_eq_representative_on_open
    (k n : ℕ) (hn : 1 ≤ n) (hnk : n ≤ k + 1)
    {x : ℝ}
    (hx : x ∈ Set.Ioo
      (selectedFerrersAbelLogSeamPoint k (n + 1))
      (selectedFerrersAbelLogSeamPoint k n)) :
    selectedFerrersAbelLogCell k n x =
      selectedFerrersAbelLogRepresentative k x

private theorem selectedFerrersAbelLogCell_upper_value
    (k n : ℕ) (hn : 1 ≤ n) (hnk : n ≤ k + 1) :
    selectedFerrersAbelLogCell k n
        (selectedFerrersAbelLogSeamPoint k n) =
      selectedFerrersAbelLogRepresentative k
        (selectedFerrersAbelLogSeamPoint k n)

private theorem selectedFerrersAbelLogCell_lower_value
    (k n : ℕ) (hn : 1 ≤ n) (hnk : n ≤ k + 1) :
    selectedFerrersAbelLogCell k n
        (selectedFerrersAbelLogSeamPoint k (n + 1)) =
      selectedFerrersAbelLogRepresentative k
          (selectedFerrersAbelLogSeamPoint k (n + 1)) -
        selectedFerrersAbelLogSeamTerm k (n + 1)

private theorem selectedFerrersAbelLogCell_last_lower_value
    (k : ℕ) :
    selectedFerrersAbelLogCell k (k + 1) 0 =
      selectedFerrersAbelLogLowerRightValue k
```

The proof must use the committed production-sum theorem and exact support. It must not redefine the public representative. `[ABSTRACT][CONDITIONAL]`

### AC and differentiability

The current execution head already supplies AC for one production term whenever its argument maps into the closed physical window, and pointwise differentiability whenever the argument lies in the open physical window. Use those suppliers to prove:

```lean
private theorem selectedFerrersAbelLogCell_absolutelyContinuousOnInterval
    (k n : ℕ) (hn : 1 ≤ n) (hnk : n ≤ k + 1) :
    AbsolutelyContinuousOnInterval
      (selectedFerrersAbelLogCell k n)
      (selectedFerrersAbelLogSeamPoint k (n + 1))
      (selectedFerrersAbelLogSeamPoint k n)

private theorem selectedFerrersAbelLogCell_differentiableAt
    (k n : ℕ) (hn : 1 ≤ n) (hnk : n ≤ k + 1)
    {x : ℝ}
    (hx : x ∈ Set.Ioo
      (selectedFerrersAbelLogSeamPoint k (n + 1))
      (selectedFerrersAbelLogSeamPoint k n)) :
    DifferentiableAt ℝ (selectedFerrersAbelLogCell k n) x

private theorem selectedFerrersAbelLogCell_intervalIntegrable_deriv
    (k n : ℕ) (hn : 1 ≤ n) (hnk : n ≤ k + 1) :
    IntervalIntegrable
      (deriv (selectedFerrersAbelLogCell k n)) volume
      (selectedFerrersAbelLogSeamPoint k (n + 1))
      (selectedFerrersAbelLogSeamPoint k n)
```

Reuse the current private complex derivative-integrability helper. Pinned Mathlib's exported `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv` is real-valued; pretending it is a complex theorem is forbidden. `[ABSTRACT][LEAN]`

Finally prove derivative agreement away from finitely many seams:

```lean
private theorem selectedFerrersAbelLogCell_deriv_ae_eq_representative
    (k n : ℕ) (hn : 1 ≤ n) (hnk : n ≤ k + 1) :
    deriv (selectedFerrersAbelLogCell k n) =ᵐ[
      volume.restrict
        (Set.Ioc
          (selectedFerrersAbelLogSeamPoint k (n + 1))
          (selectedFerrersAbelLogSeamPoint k n))]
      deriv (selectedFerrersAbelLogRepresentative k)
```

Endpoint values are irrelevant only for the integral. They are not irrelevant for the boundary telescope. `[ABSTRACT][PAPER]`

## 5. PINNED MATHLIB ENGINE

Add the direct import:

```lean
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
```

The load-bearing pinned theorem is:

```lean
theorem intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (hu : ContinuousOn u [[a, b]])
    (hv : ContinuousOn v [[a, b]])
    (huu' : ∀ x ∈ Ioo (min a b) (max a b),
      HasDerivWithinAt u (u' x) (Ioi x) x)
    (hvv' : ∀ x ∈ Ioo (min a b) (max a b),
      HasDerivWithinAt v (v' x) (Ioi x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x * v' x =
      u b * v b - u a * v a - ∫ x in a..b, u' x * v x
```

This theorem works over a complete normed real algebra, hence over `ℂ`. Full `HasDerivAt` suppliers may be weakened to the required right-within derivative. `[ABSTRACT][LEAN]`

The finite partition theorem is:

```lean
theorem intervalIntegral.sum_integral_adjacent_intervals
    {a : ℕ → ℝ} {n : ℕ}
    (hint : ∀ k < n,
      IntervalIntegrable f μ (a k) (a (k + 1))) :
    ∑ k ∈ Finset.range n,
      ∫ x in a k..a (k + 1), f x ∂μ =
        ∫ x in a 0..a n, f x ∂μ
```

The two-cell form is:

```lean
theorem intervalIntegral.integral_add_adjacent_intervals
    (hab : IntervalIntegrable f μ a b)
    (hbc : IntervalIntegrable f μ b c) :
    (∫ x in a..b, f x ∂μ) + ∫ x in b..c, f x ∂μ =
      ∫ x in a..c, f x ∂μ
```

For finite seam sets, use:

```lean
theorem IntervalIntegrable.congr_ae
    (hf : IntervalIntegrable f μ a b)
    (h : f =ᵐ[μ.restrict (Set.uIoc a b)] g) :
    IntervalIntegrable g μ a b
```

and the corresponding interval-integral a.e. congruence. `[ABSTRACT][LEAN]`

The Fourier convention is source-locked by:

```lean
lemma Real.fourier_eq (f : V → E) (w : V) :
    𝓕 f w = ∫ v, Real.fourierChar (-⟪v, w⟫) • f v
```

and

```lean
theorem Real.fourierChar_apply (x : ℝ) :
    Real.fourierChar x =
      Complex.exp (↑(2 * Real.pi * x) * Complex.I)
```

Thus the phase is exactly `exp (-2*pi*i*x*t)`. `[ABSTRACT][LEAN]`

## 6. FOURIER PHASE AND PRIMITIVE

Freeze the private phase and primitive:

```lean
private def selectedFerrersAbelLogFourierPhase
    (t x : ℝ) : ℂ :=
  (Real.fourierChar (-(x * t)) : ℂ)

private noncomputable def selectedFerrersAbelLogFourierPrimitive
    (t x : ℝ) : ℂ :=
  (((((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I)⁻¹) *
    selectedFerrersAbelLogFourierPhase t x)
```

Required lemmas:

```lean
private theorem selectedFerrersAbelLogFourierPhase_hasDerivAt
    (t x : ℝ) :
    HasDerivAt (selectedFerrersAbelLogFourierPhase t)
      ((((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I) *
        selectedFerrersAbelLogFourierPhase t x) x

private theorem selectedFerrersAbelLogFourierPrimitive_hasDerivAt
    {t : ℝ} (ht : t ≠ 0) (x : ℝ) :
    HasDerivAt (selectedFerrersAbelLogFourierPrimitive t)
      (selectedFerrersAbelLogFourierPhase t x) x

private theorem selectedFerrersAbelLogFourierPrimitive_norm
    {t : ℝ} (ht : t ≠ 0) (x : ℝ) :
    ‖selectedFerrersAbelLogFourierPrimitive t x‖ =
      1 / (2 * Real.pi * |t|)
```

Derive these from `Real.fourierChar_apply`, complex exponential differentiation, `Circle.norm_coe`, and `Real.pi_pos`. Do not fit the `2*pi` factor. `[ABSTRACT][CONDITIONAL]`

## 7. ONE-CELL IBP

For every exact cell prove:

```lean
private theorem selectedFerrersAbelLogCell_fourier_IBP
    (k n : ℕ) (hn : 1 ≤ n) (hnk : n ≤ k + 1)
    {t : ℝ} (ht : t ≠ 0) :
    (∫ x in
      selectedFerrersAbelLogSeamPoint k (n + 1)..
      selectedFerrersAbelLogSeamPoint k n,
      selectedFerrersAbelLogCell k n x *
        selectedFerrersAbelLogFourierPhase t x) =
      selectedFerrersAbelLogCell k n
          (selectedFerrersAbelLogSeamPoint k n) *
        selectedFerrersAbelLogFourierPrimitive t
          (selectedFerrersAbelLogSeamPoint k n) -
      selectedFerrersAbelLogCell k n
          (selectedFerrersAbelLogSeamPoint k (n + 1)) *
        selectedFerrersAbelLogFourierPrimitive t
          (selectedFerrersAbelLogSeamPoint k (n + 1)) -
      ∫ x in
        selectedFerrersAbelLogSeamPoint k (n + 1)..
        selectedFerrersAbelLogSeamPoint k n,
        deriv (selectedFerrersAbelLogCell k n) x *
          selectedFerrersAbelLogFourierPrimitive t x
```

Instantiate the pinned theorem with:

```text
u  = selectedFerrersAbelLogCell k n
u' = deriv (selectedFerrersAbelLogCell k n)
v  = selectedFerrersAbelLogFourierPrimitive t
v' = selectedFerrersAbelLogFourierPhase t
```

No global AC statement for the discontinuous production representative is needed. `[ABSTRACT][LEAN]`

## 8. FINITE PARTITION AND EXACT TELESCOPE

First identify the Fourier transform with the interval integral:

```lean
private theorem
    selectedFerrersAbelLogZeroExtension_fourier_eq_intervalIntegral
    (k : ℕ) (t : ℝ) :
    𝓕 (selectedFerrersAbelLogZeroExtension k) t =
      ∫ x in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
        selectedFerrersAbelLogRepresentative k x *
          selectedFerrersAbelLogFourierPhase t x
```

Unfold only through `Real.fourier_eq`, the exact indicator, `Circle.smul_def`, and the Lebesgue no-atoms conversion from `Icc` to the interval integral. `[ABSTRACT][LEAN]`

Then prove the finite partition:

```lean
private theorem selectedFerrersAbelLogFourierIntegral_eq_cellPartition
    (k : ℕ) (t : ℝ) :
    (∫ x in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
      selectedFerrersAbelLogRepresentative k x *
        selectedFerrersAbelLogFourierPhase t x) =
      ∑ j ∈ Finset.range (k + 1),
        ∫ x in
          selectedFerrersAbelLogPartitionPoint k j..
          selectedFerrersAbelLogPartitionPoint k (j + 1),
          selectedFerrersAbelLogCell k (k + 1 - j) x *
            selectedFerrersAbelLogFourierPhase t x
```

Use `sum_integral_adjacent_intervals` on the production integrand and replace each cell only almost everywhere. The closed endpoint mismatch is not rewritten pointwise. `[ABSTRACT][LEAN]`

The boundary terms must telescope before taking norms:

```lean
private theorem selectedFerrersAbelLogCellBoundary_telescope
    (k : ℕ) (t : ℝ) :
    (∑ j ∈ Finset.range (k + 1),
      (selectedFerrersAbelLogCell k (k + 1 - j)
          (selectedFerrersAbelLogPartitionPoint k (j + 1)) *
        selectedFerrersAbelLogFourierPrimitive t
          (selectedFerrersAbelLogPartitionPoint k (j + 1)) -
       selectedFerrersAbelLogCell k (k + 1 - j)
          (selectedFerrersAbelLogPartitionPoint k j) *
        selectedFerrersAbelLogFourierPrimitive t
          (selectedFerrersAbelLogPartitionPoint k j))) =
      selectedFerrersAbelLogRepresentative k
          (L_m (selectedFerrersPreAnchorIndex k)) *
        selectedFerrersAbelLogFourierPrimitive t
          (L_m (selectedFerrersPreAnchorIndex k)) -
      selectedFerrersAbelLogLowerRightValue k *
        selectedFerrersAbelLogFourierPrimitive t 0 +
      ∑ n ∈ Finset.Icc 2 (k + 1),
        selectedFerrersAbelLogSeamTerm k n *
          selectedFerrersAbelLogFourierPrimitive t
            (selectedFerrersAbelLogSeamPoint k n)
```

The internal full values cancel algebraically. The surviving internal term is exactly the entering seam. The lower `n=k+2` seam is already inside `selectedFerrersAbelLogLowerRightValue`; it is not included in the internal sum. `[ABSTRACT][PAPER]`

Also prove the derivative-budget crosswalk:

```lean
private theorem selectedFerrersAbelLogDerivativeBudget_eq_cellPartition
    (k : ℕ) :
    selectedFerrersAbelLogDerivativeBudget k =
      ∑ j ∈ Finset.range (k + 1),
        ∫ x in
          selectedFerrersAbelLogPartitionPoint k j..
          selectedFerrersAbelLogPartitionPoint k (j + 1),
          ‖deriv
            (selectedFerrersAbelLogCell k (k + 1 - j)) x‖
```

This equality is an a.e. statement. Do not assert derivative equality at seams. `[ABSTRACT][LEAN]`

## 9. SHARP PRIVATE ESTIMATE, THEN SAFE PUBLIC LEDGER

The exact telescope must first yield:

```lean
private theorem
    selectedFerrersAbelLogZeroExtension_fourier_decay_off_zero_sharp
    (k : ℕ) {t : ℝ} (ht : t ≠ 0) :
    ‖𝓕 (selectedFerrersAbelLogZeroExtension k) t‖ ≤
      (selectedFerrersAbelLogDerivativeBudget k +
        ‖selectedFerrersAbelLogLowerRightValue k‖ +
        ‖selectedFerrersAbelLogRepresentative k
          (L_m (selectedFerrersPreAnchorIndex k))‖ +
        ∑ n ∈ Finset.Icc 2 (k + 1),
          ‖selectedFerrersAbelLogSeamTerm k n‖) /
      (2 * Real.pi * |t|)
```

Only after this theorem may the proof use

```lean
selectedFerrersAbelLogLowerRightValue_norm_le
```

and

```lean
selectedFerrersAbelLogLowerEndpointSeam_eq_lastSummand.
```

Freeze the finite-ledger split:

```lean
private theorem selectedFerrersAbelLogJumpBudget_eq_internal_add_lower
    (k : ℕ) :
    selectedFerrersAbelLogJumpBudget k =
      ‖selectedFerrersAbelLogRepresentative k 0‖ +
      ‖selectedFerrersAbelLogRepresentative k
        (L_m (selectedFerrersPreAnchorIndex k))‖ +
      (∑ n ∈ Finset.Icc 2 (k + 1),
        ‖selectedFerrersAbelLogSeamTerm k n‖) +
      ‖selectedFerrersAbelLogLowerEndpointSeam k‖
```

Associative parenthesization may differ; the summand set and the separate lower term may not. `[ABSTRACT][CONDITIONAL]`

This closes the frozen public theorem:

```lean
theorem selectedFerrersAbelLogZeroExtension_fourier_decay_off_zero
    (k : ℕ) {t : ℝ} (ht : t ≠ 0) :
    ‖𝓕 (selectedFerrersAbelLogZeroExtension k) t‖ ≤
      (selectedFerrersAbelLogDerivativeBudget k +
        selectedFerrersAbelLogJumpBudget k) /
      (2 * Real.pi * |t|)
```

`[ABSTRACT][CONDITIONAL]`

## 10. GLOBAL FIXED-`k` DECAY

Add only private support:

```lean
private theorem selectedFerrersAbelLogZeroExtension_integrable
    (k : ℕ) :
    Integrable (selectedFerrersAbelLogZeroExtension k) volume
```

The proof may reuse the same finite cell partition. No new public `L¹` object is required. `[ABSTRACT][CONDITIONAL]`

Use the pinned bound

```lean
theorem VectorFourier.norm_fourierIntegral_le_integral_norm
    (e) (μ) (L) (f) (w) :
    ‖VectorFourier.fourierIntegral e μ L f w‖ ≤
      ∫ v, ‖f v‖ ∂μ
```

near `t=0`. Let

\[
A_k=\int_{\mathbb R}\|G_k(x)\|\,dx,
\qquad
D_k=\frac{\operatorname{DerivativeBudget}_k+\operatorname{JumpBudget}_k}{2\pi},
\]

and choose privately

\[
C_k=2(A_k+D_k).
\]

For `|t|≤1`, use the `L¹` bound and `1+|t|≤2`. For `1≤|t|`, use the off-zero theorem and `1+|t|≤2|t|`. This proves exactly:

```lean
theorem selectedFerrersAbelLogZeroExtension_fourier_decay
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ,
        ‖𝓕 (selectedFerrersAbelLogZeroExtension k) t‖ ≤
          C / (1 + |t|)
```

The quantifier spine remains `forall k, exists C_k, forall t`. `[ABSTRACT][CONDITIONAL]`

## 11. MANDATORY PLANTS

The same Lean source must contain and print the axioms of these private plants.

### Plant 1 — exact cells are not seam-free

```lean
private theorem selectedFerrersAbelLogClosedCell_not_seamFree_plant
    (k : ℕ) :
    ¬ selectedFerrersAbelLogSeamFreeOn k 0
      (selectedFerrersAbelLogSeamPoint k (k + 1))
```

Witness the failure at `x=0`, `n=k+2`. This prevents the false shortcut through the existing seam-free theorem. `[ABSTRACT][LEAN]`

### Plant 2 — lower seam cannot be absorbed

```lean
private theorem selectedFerrersAbelLogLowerRight_norm_shortcut_false_plant :
    ¬ ∀ a b : ℂ, ‖a - b‖ ≤ ‖a‖
```

Use `a=0`, `b=1`. `[ABSTRACT][LEAN]`

### Plant 3 — one internal seam survives telescope

```lean
private theorem selectedFerrersAbelLogTwoCell_telescope_plant
    (g J p A B : ℂ) :
    (g * p - A) + (B - (g - J) * p) =
      B - A + J * p := by
  ring
```

This catches a sign reversal that would erase rather than retain the seam. `[ABSTRACT][LEAN]`

### Plant 4 — Fourier normalization

Print the axioms of `selectedFerrersAbelLogFourierPrimitive_hasDerivAt`. The derivative must be the exact `Real.fourierChar` phase, not a fitted or sign-flipped exponential. `[ABSTRACT][LEAN]`

## 12. REJECTED ALTERNATIVES

Do not use any of the following in this transaction:

```text
ε-trim every cell and pass ε→0;
apply seam-free AC to closed seam cells;
replace the full-endpoint representative by a midpoint representative;
assume h_k(lambda_k)=0;
assume norm(g_k(0+)) <= norm(g_k(0));
import W3 private seam names as APIs;
create a public seam-partition supplier module;
use a global Fourier-transform derivative theorem instead of the frozen hand-written IBP;
start shifted form-domain assembly;
start W5.
```

These moves either change the source object, add unnecessary topology, violate privacy, or bypass the exact repaired ledger. `[ABSTRACT][PAPER]`

## 13. PROOF ORDER

Implement in this order and stop on the first exact gap:

```text
1. Add the direct IntegrationByParts import.
2. Prove seam arithmetic and the closed-cell-not-seam-free plant.
3. Define active indices, seam terms and closed cells.
4. Prove interior, upper and lower value identities.
5. Prove closed-cell AC, interior differentiability and derivative integrability.
6. Prove Fourier phase/primitive derivative and norm.
7. Prove one-cell IBP from the pinned theorem.
8. Prove Fourier interval identity and finite partition.
9. Prove boundary telescope before any norm inequality.
10. Prove derivative-budget a.e. partition.
11. Prove the sharp lower-right off-zero estimate.
12. Split the repaired public jump budget and prove the frozen public off-zero theorem.
13. Prove zero-extension integrability and the global fixed-k theorem.
14. Print axioms for all five public theorems and all plants.
```

`[ABSTRACT][CONDITIONAL]`

## 14. VALIDATION GATE

### WORKDIR: `q3.lean.aristotle`

```bash
lake env lean \
  Q3/Proofs/RouteB/G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean
```

```bash
lake build \
  Q3.Proofs.RouteB.G6N1SelectedFerrersPiecewiseACDerivativeIntegrability
```

### WORKDIR: repository root

```bash
scripts/q3_check.sh \
  Q3/Proofs/RouteB/G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean
```

Every printed public theorem and plant must have exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Kernel-green success token:

```text
W4_ZERO_ENDPOINT_JUMP_LEDGER_REPAIRED_AND_FIXED_K_FOURIER_DECAY_KERNEL_GREEN
```

This token is not semantic admission and does not authorize the downstream assembly. `[ABSTRACT][LEAN]`

Failure codes:

```text
W4_EXACT_CELL_SEAM_GEOMETRY_GAP
W4_ACTIVE_INDEX_CELL_VALUE_GAP
W4_FIXED_ACTIVE_CELL_AC_GAP
W4_CELL_INTERIOR_DIFFERENTIABILITY_GAP
W4_PINNED_IBP_API_GAP
W4_FOURIER_INTERVAL_CROSSWALK_GAP
W4_FINITE_PARTITION_REINDEX_GAP
W4_TELESCOPE_ORIENTATION_GAP
W4_DERIVATIVE_BUDGET_AE_CROSSWALK_GAP
W4_N_EQ_K_PLUS_2_PAYMENT_GAP
W4_ZERO_EXTENSION_L1_GAP
W4_PUBLIC_SURFACE_EXPANSION
W4_KERNEL_OR_AXIOM_PROFILE_GAP
```

A failure does not authorize changing the public theorem, switching endpoint convention, creating a public supplier, or starting a downstream node. `[ABSTRACT][PAPER]`

## FINAL PROPOSAL

Proceed with one source-preserving Lean transaction in the existing W4 file. Build exact right-continuous fixed-active cells, apply pinned complex interval integration by parts on each cell, telescope the full endpoint values before taking norms, and pay the lower right representative by the existing full value plus the exact `n=k+2` final summand. `[ABSTRACT][PAPER]`

The current four additive helper commits are useful and should remain. They already supply the production-term AC and differentiability pieces. Do not duplicate them and do not widen their visibility. `[ABSTRACT][LEAN]`

### Registered predictions before the remaining source test

```text
P_W4_IBP_1:
  p = 0.76
  The fixed-active cell architecture proves the frozen off-zero theorem without
  changing the public statement or representative.

P_W4_IBP_2:
  p = 0.84
  The first implementation failure, if any, is Nat/Finset reindexing or an
  interval-integral normal-form mismatch, not a mathematical counterexample.

P_W4_IBP_3:
  p = 0.95
  The existing lower-seam helper and the finite Icc split pay n=k+2 exactly.

P_W4_IBP_4:
  p = 0.97
  A green completed source has exactly the standard axiom triple on every
  printed theorem and plant.
```

## STRONGEST ATTACK

The strongest objection is that the private cell is not literally the public production representative at its lower endpoint. That objection is correct and is the entire reason the cell is needed. Fourier integration and derivative budgets ignore finitely many point values, but integration by parts consumes explicit endpoint representatives. The cell must therefore use the right-hand value at its lower endpoint while retaining the exact full production value at its upper endpoint. `[ABSTRACT][PAPER]`

This does not change the public object. The source must prove three separate facts: equality on the open cell, exact full value at the upper endpoint, and exact full-minus-one-seam value at the lower endpoint. C04 forbids collapsing those three categories into one pointwise equality. `[ABSTRACT][PAPER]`

A second objection is that the public derivative budget uses `deriv` of the discontinuous production representative, while IBP uses derivatives of private cells. The repair is an a.e. derivative crosswalk on each open cell plus the no-atoms finite partition. Any proof that rewrites derivatives at seam points is stronger than needed and likely false. `[ABSTRACT][PAPER]`

A third objection is double counting the lower seam. The exact sharp theorem uses `g_k(0+)` and only internal seams `2..k+1`. The safe public theorem replaces `g_k(0+)` by `g_k(0)` plus the separate last term `k+2`. This order is mandatory and mechanically falsifiable. `[ABSTRACT][PAPER]`

## CODEX DIRECTIVE

```text
TASK_ID:
  H2A_4_1B_3C_1_13A_W4_FINITE_SEAM_TELESCOPE_IBP_LEAN

MODE:
  CONTINUE_EXISTING_W4_FILE_ONE_KERNEL_NODE

BASE:
  use current rh_clean;
  preserve every additive private supplier after source pin 92e03a66;
  do not reset the file to the old pin.

EDIT EXACTLY:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean

ADD IN SAME COMMIT:
  docs/routeB_bus/CODEX_SOURCE_RECORD_2026_08_24_W4_FINITE_SEAM_TELESCOPE_IBP.md

OBJECTIVE:
  implement the private theorem packet in this verdict;
  prove the two missing frozen public Fourier-decay theorems;
  preserve the exact production full-endpoint complex object;
  preserve Finset.Icc 2 (k+2) in the public jump budget.

DIRECT IMPORT TO ADD:
  Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

DO NOT:
  edit W2 or W3;
  expose a new public helper;
  call private declarations across modules;
  use an epsilon-limit partition;
  use midpoint regularization;
  weaken the quantifier spine;
  start G6N1SelectedFerrersFixedKShiftedRootEnergy.lean;
  perform W5 work;
  promote Route B;
  make an RH claim.

STOP ON FIRST EXACT GAP AND REPORT:
  theorem being proved;
  exact goal state category;
  pinned Mathlib theorem attempted;
  smallest missing private lemma;
  whether the failure is geometry, API, reindexing, telescope orientation,
  derivative a.e. transport, or public-ledger payment.
```

## META CLOSEOUT

**What became smaller?**

The blocker is reduced from generic piecewise AC/Fourier decay to one finite source-addressed cell partition and telescope. The production-term derivative and closed-cell AC engines are already committed privately. `[ABSTRACT][PAPER]`

**What was killed?**

- direct use of seam-free AC on exact closed cells;
- epsilon-trim plus limit as the primary route;
- any midpoint or endpoint-zero surrogate;
- any proof that takes norms before the seam telescope.

**What must not be tried again?**

Do not treat a full endpoint value, a one-sided representative, and an a.e. function as the same object. Do not rewrite derivative values at seams. Do not absorb the lower seam without its final public summand. `[ABSTRACT][PAPER]`

**Current smallest named gap?**

```text
W4_FINITE_SEAM_TELESCOPE_IBP_LEAN
```

**Next cheapest decisive test?**

Compile the seam geometry, exact cell endpoint identities, and the one-cell IBP theorem before implementing the global telescope. `[ABSTRACT][CONDITIONAL]`

**Fate of prior registered predictions**

```text
P_W4_SOURCE_FORK_1:
  CONFIRMED.
  Private local reconstruction reached the frozen packet-AC theorem without a
  public supplier.

P_W4_SOURCE_FORK_2:
  CONFIRMED.
  The remaining obstruction is the predicted complex AC/IBP and finite
  normal-form layer, not a counterexample to packet Lipschitzness.

P_W4_SOURCE_FORK_3:
  OWNER_REPORTED_CONFIRMED_FOR_AC_PREFIX; JUDGE_NOT_RERUN.
  The completed five-theorem node remains unscored.
```

**Memory entry**

```yaml
iteration: W4_finite_seam_telescope_IBP_architecture
target: W4_FINITE_SEAM_TELESCOPE_IBP_LEAN
status: OPEN_AUTHORIZED
failed_strategy: CLOSED_CELL_VIA_SEAM_FREE_PREDICATE
cognitive_operator_used: BOUNDARY_CASE
new_gap_name: W4_FINITE_SEAM_TELESCOPE_IBP_LEAN
invariant_learned: endpoint_full_value_right_limit_and_ae_representative_are_distinct
forbidden_future_move: norm_before_telescope_or_omit_n_eq_k_plus_2
next_decisive_test: kernel_gate_through_one_cell_IBP
```
