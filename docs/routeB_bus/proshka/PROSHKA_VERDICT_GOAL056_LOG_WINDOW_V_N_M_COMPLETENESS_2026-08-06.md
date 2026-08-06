# STATUS: OPEN — SOURCE-LOCKED LOG-WINDOW UNITARY AND LITERAL `V_n_m` HILBERT BASIS SELECTED

```yaml
PRIMARY: G6_S2_D0_LOG_WINDOW_V_N_M_COMPLETENESS_BRIDGE_SELECTED
PRIMARY_COUNT: 1

OPERATIVE_CLASS: TRY_G6_S2_D0_LOG_WINDOW_V_N_M_COMPLETENESS_BRIDGE
OPERATIVE_CLASS_COUNT: 1

CANDIDATE:
  SELECTED: A_REPAIRED_LOG_WINDOW_UNITARY_PLUS_INTERVAL_PARSEVAL_TOTALITY
  ORIGINAL_A_DIRECT_ADD_CIRCLE_BASIS_TRANSPORT: REPAIRED
  B_PRIVATE_TOTALITY_ONLY: REJECTED_AS_NO_SMALLER
  C_COMPLETENESS_AS_SOURCE_DATA: KILLED_C09_C10

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  PIN: 6d4dd030a0fe9724065b7f74f7da8e2cfadf331e
  ORIGIN_HEAD_EQUALS_PIN: true
  COMMIT: "[MacOS][rh_clean][Docs] Research Goal 056 V_n_m completeness"

HASH_AUDIT:
  D0LogWindowMeasureTransport:
    EXPECTED_SHA256: 59c6d9a3a3a3c77427997665216e3ff797b9e2dc925cb63e5e9e6df0df64905b
    STATUS: TRACKED_CLOSEOUT_AND_CONTENT_MATCH
  D0KTrialStage1:
    EXPECTED_SHA256: c7dd206ab7979d3390a50969c71919c04582f0c1514dbb142fe1883148ce5b48
    STATUS: SUPPLIED_DISK_HASH_ACCEPTED_CURRENT_CONTENT_AND_SOURCE_LOCK_MATCH
  D0HilbertBasisWeightedTail:
    EXPECTED_SHA256: 24956f668098ea0a940ba50ebdd4087d7645114c8c0919a5587f35f10135643c
    STATUS: TRACKED_CLOSEOUT_AND_CONTENT_MATCH
  INSIGHTS:
    EXPECTED_SHA256: f46fb47fc5cab9452d87e7afee06b89edbf7f592396c3ced80a982390f6e0341
    STATUS: SUPPLIED_DISK_HASH_ACCEPTED_EXACT_PIN_DIFF_MATCH
  FRESH_INDEPENDENT_BYTE_REHASH_BY_REVIEWER: false
  HASH_MISMATCH_OBSERVED: false

PREDECESSOR:
  COMMIT: 8c4db9f874e342829d595e36f775d51fc6f19b9d
  RESULT: G6_S2_D0_GENERIC_HILBERT_BASIS_PARSEVAL_AND_WEIGHTED_TAIL_PROVED
  STATUS: CLOSED
  REOPENED: false

ARSENAL:
  MANDATE_ACCEPTED: true
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

TRANSACTION:
  NAME: G6_S2_D0_LOG_WINDOW_V_N_M_COMPLETENESS_BRIDGE
  OWNED_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0LogWindowVNMCompletenessBridge.lean
  NAMESPACE: Q3.RouteB.D0Pstar
  PUBLIC_DEFINITIONS: 2
  PUBLIC_THEOREMS: 3
  PRIVATE_THEOREMS: 3
  PRIVATE_DEFINITIONS: 0

D0_HILBERT_BASIS_WEIGHTED_TAIL_IMPORTED_NOW: true
IMMEDIATE_UNWEIGHTED_MODESET_RESIDUAL_IDENTITY: authorized
PHYSICAL_WEIGHTED_ENERGY_CONTROL: forbidden_in_this_transaction

STOP: G6_S2_D0_LOG_WINDOW_V_N_M_COMPLETENESS_BRIDGE_MISSING
SUCCESS: G6_S2_D0_LOG_WINDOW_V_N_M_HILBERT_BASIS_AND_COMPLEMENT_PARSEVAL_PROVED

SOLE_NEXT_NODE_NOT_AUTHORIZED:
  G6_S2_D0_SELECTED_PHYSICAL_FOURIER_ENERGY_CONTROL

PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

PHASE_KEY_CHANGE: false
REUSE_CONVERSATION_ID: 6a72e750-dc60-83eb-946b-61d2073c232b
FRESH_CHAT: false

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ARISTOTLE_SUBMISSION: NONE
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## 1. Source-lock audit

The live branch ref resolves exactly to `6d4dd030a0fe9724065b7f74f7da8e2cfadf331e`. The commit is the stated research-only Phase-4K entry and modifies only `INSIGHTS.md`; it records the precise completeness fork without adding production mathematics.   `[ABSTRACT][PAPER]`

The earlier attached Phase-4I packet remains useful historical context, but its older pin is not controlling here; the current GitHub pin and current production files govern this adjudication.  `[ABSTRACT][PAPER]`

Phase 4J is closed exactly as reported. It proves the generic complement Parseval identity and weighted receiver for an already-complete `HilbertBasis`; it explicitly does not prove completeness of `V_n_m`, physical-frequency control, selected projection-tail decay, or `SlotS2`. Its production SHA-256 and all validation gates are recorded in the closeout.   `[ABSTRACT][LEAN]`

Phase 4C is also intact. It proves the scalar logarithmic change of variables and literal orthonormality of `V_n_m`, preserving the exact `du/u` density, `log (lambda_m*u)` orientation, (L_m^{-1/2}) normalization, and conjugate-linear-first phase.  `[ABSTRACT][LEAN]`

The source-locked definitions remain:

```text
H_m i = L²(Icc(lambda_m⁻¹,lambda_m), du/u)

V_n_m i n =
  L_m⁻¹ᐟ² · exp(2π i n log(lambda_m*u)/L_m)

E_m_N i =
  span {V_n_m i n : n ∈ modeSet i}

P_m_N i =
  orthogonal projection onto E_m_N i.
```

`[ABSTRACT][LEAN]`

The D0.1 source contract separately fixes the full unitary—not merely an integral identity:

[
\kappa_m:
L^2([0,L_m],dx)\longrightarrow H_m,
\qquad
(\kappa_m f)(u)=f(\log(\lambda_m u)),
]

with inverse (g\mapsto[x\mapsto g(e^x/\lambda_m)]). It also fixes the exact normalized Fourier modes and the antilinear-first inner-product convention.  `[ABSTRACT][PAPER]`

### Hash qualification

No mismatch was found among the four supplied SHA-256 locks.

The Phase-4C and Phase-4J hashes are independently reproduced in tracked closeout records. The current connector exposes repository contents and Git blob hashes, not a local SHA-256 byte-stream operation; therefore the `D0KTrialStage1` and current `INSIGHTS.md` values are accepted from the verified disk report together with exact current-content and commit-diff cross-checks. I do not relabel that as a fresh independent byte rehash.

## 2. Audit of the temporary `logWindow_map` proof

The scratch theorem

```lean
Measure.map (fun u => Real.log (lambda_m i * u))
    (dStar.restrict (I_m i))
  =
volume.restrict (Set.Icc 0 (L_m i))
```

is mathematically correct and is the decisive forward measure theorem.

Pinned Mathlib contains the exact Jacobian API used by the scratch:

```lean
map_withDensity_abs_det_fderiv_eq_addHaar
```

which pushes the input measure weighted by the absolute derivative onto Lebesgue measure on the image set. For

[
\phi_i(u)=\log(\lambda_i u),
\qquad
\phi_i'(u)=u^{-1},
]

its input measure is exactly `dStar.restrict (I_m i)`, and its image is exactly `Icc 0 (L_m i)`.  `[ABSTRACT][LEAN]`

It is sufficient to build the forward `Lp` linear isometry:

```lean
Lp ℂ 2 (volume.restrict (Icc 0 L_m))
  →ₗᵢ[ℂ]
H_m i.
```

It is **not by itself sufficient** to construct the required `LinearIsometryEquiv`.

Three technical obligations remain:

1. prove the inverse map
   [
   \psi_i(x)=e^x/\lambda_i
   ]
   is measure-preserving in the reverse direction;

2. prove
   [
   \psi_i\circ\phi_i=\mathrm{id}
   \quad\text{and}\quad
   \phi_i\circ\psi_i=\mathrm{id}
   ]
   almost everywhere under the two restricted measures;

3. reconcile `Icc 0 L_m`, used by the source unitary, with `Ioc 0 L_m`, used by Mathlib’s interval Fourier API, by an explicit null-endpoint measure equality.

These are local measure/API obligations. They require no new source hypothesis or analytic estimate.

Pinned Mathlib already provides:

```lean
Lp.compMeasurePreserving
Lp.coeFn_compMeasurePreserving
Lp.compMeasurePreservingₗᵢ
LinearIsometryEquiv.ofLinearIsometry
```

with exactly the directions required to assemble the equivalence from two composition maps.   `[ABSTRACT][LEAN]`

## 3. Load-bearing normalization attack

The original wording of Candidate A contains one real trap:

> “Transport Mathlib’s `fourierBasis` from `AddCircle (L_m i)` directly to the interval and then to `H_m`.”

Mathlib’s `fourierBasis` is orthonormal for **normalized Haar measure of total mass one**. The ordinary `volume` measure on `AddCircle T` has total mass (T), with:

[
\mathrm{volume}
===============

T\cdot\mathrm{haarAddCircle}.
]

`[ABSTRACT][LEAN]`

Consequently:

* the raw circle monomial (e^{2\pi i nx/T}) has norm one under normalized Haar;
* the same monomial has norm (\sqrt T) under interval Lebesgue measure;
* the literal production mode requires the factor (T^{-1/2}).

Mathlib’s interval Parseval theorem records the same normalization explicitly:

[
\sum_n |\widehat f(n)|^2
========================

\frac1{b-a}\int_a^b |f(x)|^2,dx.
]

`[ABSTRACT][LEAN]`

Therefore direct transport of `AddCircle.fourierBasis` without a separate Haar-to-volume scaling equivalence would lose or double-count the factor (L_m^{-1/2}).

That is a **C04** failure: normalized Haar and unnormalized interval volume use the same coordinate functions under different measure laws.

It is not fatal to Candidate A. It forces the following repair:

```text
publish the source-locked log-window Lp equivalence;
prove totality of the literal normalized interval modes by interval Parseval;
construct the Hilbert basis with HilbertBasis.mkOfOrthogonalEqBot.
```

This avoids a second measure-scaling layer while preserving the canonical unitary.

## 4. A–C comparison

| Candidate                                                               | Mathematical honesty        | Lean executability                          | Source fidelity                 |      Public surface | Hidden work                                                                  | Verdict                          |
| ----------------------------------------------------------------------- | --------------------------- | ------------------------------------------- | ------------------------------- | ------------------: | ---------------------------------------------------------------------------- | -------------------------------- |
| **A, repaired: public log-window unitary + interval Parseval totality** | Exact D0.1 object           | High; forward map already compiled          | Highest                         |            Moderate | Inverse map, a.e. compositions, coefficient normalization                    | **SELECTED**                     |
| **B: private unitary / direct orthogonal-complement proof**             | Correct                     | Comparable                                  | Hides the canonical D0.1 bridge |    Slightly smaller | Essentially the same inverse, representative, endpoint, and coefficient work | Rejected as not actually smaller |
| **C: completeness as source-data field**                                | Assumes the missing theorem | Easy only because the theorem is postulated | Invalid                         | Structure migration | All mathematics hidden                                                       | **KILLED — C09/C10**             |

### Candidate B

Candidate B still has to:

* move arbitrary `H_m` elements into logarithmic coordinates;
* handle quotient representatives almost everywhere;
* prove the exact coefficient formula;
* reconcile `Icc` and `Ioc`;
* invoke Parseval.

Keeping the unitary private saves one public definition but causes the same proof cost and forces the next physical-energy transaction to reconstruct the map.

### Candidate C

Adding a field asserting that `V_n_m` is complete would be a post hoc strengthening after the consumer was known. It would also replace a source theorem by a structure premise. This is precisely the **C09 precommit** and **C10 functional/surrogate** failure prohibited by the Arsenal mandate.   `[ABSTRACT][PAPER]`

## 5. Selected production file and imports

Owned file:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0LogWindowVNMCompletenessBridge.lean
```

Exact imports:

```lean
import Q3.Proofs.RouteB.D0FiniteProjectionReconstruction
import Q3.Proofs.RouteB.D0HilbertBasisWeightedTail
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.Jacobian
```

Namespace:

```lean
namespace Q3.RouteB.D0Pstar
```

This file becomes the first current production importer of:

```text
Q3.Proofs.RouteB.D0HilbertBasisWeightedTail
```

The import is immediately consumed by the unweighted source-specific residual identity. It is not a dormant import.

### Exact surface

```yaml
public_definitions: 2
public_theorems: 3
private_theorems: 3
private_definitions: 0
```

All additional arithmetic, endpoint, representative, and composition facts must remain local `let`/`have` declarations inside those proofs.

## 6. Exact public declarations

### 6.1 Source-locked logarithmic (L^2) equivalence

```lean
/--
The exact D0.1 unitary
`f(x) ↦ f (log (lambda_m i * u))`
from the additive log window to the multiplicative `H_m` carrier.
-/
noncomputable def logWindowL2Equiv (i : PairIndex) :
    MeasureTheory.Lp ℂ 2
        (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))
      ≃ₗᵢ[ℂ]
    H_m i := by
  ...
```

`[ABSTRACT][CONDITIONAL]`

After compilation: `[ABSTRACT][LEAN]`.

This definition is not excess surface. It is the exact source object `kappa_m`, is consumed by the completeness proof, and is the natural input for the later physical derivative/Fourier-energy crosswalk.

### 6.2 Exact representative formula

```lean
theorem coeFn_logWindowL2Equiv
    (i : PairIndex)
    (f : MeasureTheory.Lp ℂ 2
      (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))) :
    ((logWindowL2Equiv i f : H_m i) : ℝ → ℂ)
      =ᵐ[dStar.restrict (I_m i)]
        (fun u : ℝ =>
          f (Real.log (lambda_m i * u))) := by
  ...
```

`[ABSTRACT][CONDITIONAL]`

This theorem must remain an almost-everywhere statement. A global pointwise statement about arbitrary `Lp` representatives is false as an object claim.

### 6.3 Literal Hilbert basis

```lean
/--
The literal production modes `V_n_m i n`, with no phase or measure change,
form a complete Hilbert basis of `H_m i`.
-/
noncomputable def V_n_m_hilbertBasis (i : PairIndex) :
    HilbertBasis ℤ ℂ (H_m i) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (V_n_m_orthonormal i)
    (V_n_m_span_orthogonal_eq_bot i)
```

`[ABSTRACT][CONDITIONAL]`

Pinned Mathlib provides both `HilbertBasis.mkOfOrthogonalEqBot` and its literal-value simp theorem.  `[ABSTRACT][LEAN]`

### 6.4 Literal basis-value lock

```lean
@[simp] theorem V_n_m_hilbertBasis_apply
    (i : PairIndex) (n : ℤ) :
    V_n_m_hilbertBasis i n = V_n_m i n := by
  simp [V_n_m_hilbertBasis]
```

`[ABSTRACT][CONDITIONAL]`

The result must be equality to the existing `V_n_m`, not merely existence of an equivalent or phase-twisted basis.

### 6.5 Immediate unweighted residual identity

```lean
theorem norm_sub_coe_P_m_N_sq_eq_tsum_complement
    (i : PairIndex) (f : H_m i) :
    ‖f - (P_m_N i f : H_m i)‖ ^ 2 =
      ∑' n : ℤ,
        if n ∈ modeSet i then 0
        else ‖inner ℂ (V_n_m i n) f‖ ^ 2 := by
  rw [coe_P_m_N_apply_eq_sum_inner_V_n_m_smul]
  simpa [V_n_m_hilbertBasis_apply] using
    norm_sub_basisPartialSum_sq_eq_tsum
      (V_n_m_hilbertBasis i)
      (modeSet i)
      f
```

`[ABSTRACT][CONDITIONAL]`

This theorem belongs in the transaction.

It is a pure exact consumer of:

* Phase 4D finite reconstruction;
* Phase 4J complement Parseval;
* the newly proved literal basis equality.

It chooses no physical weight, supplies no rate, and proves no selected-family limit. Omitting it would manufacture an artificial one-line boundary.

## 7. Exact private declarations

```lean
private theorem logWindow_measurePreserving
    (i : PairIndex) :
    MeasurePreserving
      (fun u : ℝ => Real.log (lambda_m i * u))
      (dStar.restrict (I_m i))
      (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) := by
  ...
```

```lean
private theorem expWindow_measurePreserving
    (i : PairIndex) :
    MeasurePreserving
      (fun x : ℝ => Real.exp x / lambda_m i)
      (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))
      (dStar.restrict (I_m i)) := by
  ...
```

```lean
private theorem V_n_m_span_orthogonal_eq_bot
    (i : PairIndex) :
    (Submodule.span ℂ (Set.range (V_n_m i)))ᗮ = ⊥ := by
  ...
```

The reverse measure theorem should preferably be derived from the forward pushforward and the two almost-everywhere inverse identities. It must not introduce a second independently normalized Jacobian convention.

## 8. Concrete implementation route

### Step 1 — window arithmetic

Locally prove:

```text
1 < lambda_m i;
0 < lambda_m i;
0 < L_m i;
lambda_m i * lambda_m i = i.m.
```

These facts already occur in Phase 4C but are private there, so this file must either derive them locally or use newly exposed existing public facts if Codex finds them.

### Step 2 — forward measure preservation

Set:

```lean
φ u := Real.log (lambda_m i * u).
```

Use:

```lean
MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar
```

with:

```text
source set = I_m i;
derivative = u⁻¹;
image = Icc 0 (L_m i);
injective on the positive window.
```

Rewrite the input measure through:

```text
dStar;
Measure.restrict_withDensity.
```

This closes `logWindow_measurePreserving`.

### Step 3 — reverse measure preservation

Set:

```lean
ψ x := Real.exp x / lambda_m i.
```

Prove under the restricted measures:

```text
ψ (φ u) = u     μ-a.e.;
φ (ψ x) = x     ν-a.e.
```

Then use pushforward composition and `Measure.map_congr`/`Measure.map_map` to derive:

```text
Measure.map ψ ν = μ.
```

Do not claim the identities globally outside the restricted supports.

### Step 4 — build `logWindowL2Equiv`

The forward linear isometry is:

```lean
MeasureTheory.Lp.compMeasurePreservingₗᵢ
  ℂ φ (logWindow_measurePreserving i)
```

and the inverse linear map comes from composition with `ψ`.

Construct the equivalence through:

```lean
LinearIsometryEquiv.ofLinearIsometry
```

and prove both compositions using:

```lean
MeasureTheory.Lp.ext
MeasureTheory.Lp.coeFn_compMeasurePreserving
```

plus the almost-everywhere inverse identities.   `[ABSTRACT][LEAN]`

### Step 5 — prove the public representative theorem

Use the pinned theorem:

```lean
Lp.coeFn_compMeasurePreserving
```

directly. No pointwise representative selection is permitted.

### Step 6 — prove totality

Let:

```text
x ∈ (span ℂ (range (V_n_m i)))ᗮ
g := (logWindowL2Equiv i).symm x.
```

For each (n), orthogonality gives:

[
\langle V_{n,m},x\rangle=0.
]

Transporting through the unitary gives the additive-coordinate coefficient.

The exact coefficient law is:

[
\boxed{
\langle U_{n,m},g\rangle
========================

\sqrt{L_m},
\operatorname{fourierCoeffOn}_{[0,L_m]}(g,n).
}
]

The sign is fixed:

* `V_n_m` uses (+2\pi i n x/L_m);
* the inner product conjugates its first argument;
* `fourierCoeffOn` uses the (-n) Fourier monomial.

Thus no sign flip is required.

Next, explicitly prove:

```text
volume.restrict (Icc 0 L_m)
=
volume.restrict (Ioc 0 L_m).
```

This equality is measure-theoretic only; endpoint values are not identified pointwise.

Apply:

```lean
AddCircle.hasSum_sq_fourierCoeffOn
```

or its unqualified theorem name at the pinned import. Since every Fourier coefficient is zero, Parseval gives zero `L²` norm, hence `g = 0`, hence `x = 0`.

This proves:

```lean
V_n_m_span_orthogonal_eq_bot.
```

### Step 7 — construct the literal basis

Use:

```lean
HilbertBasis.mkOfOrthogonalEqBot
```

with the already-proved `V_n_m_orthonormal i`.

### Step 8 — consume Phase 4J immediately

Prove the unweighted projection-complement identity by rewriting Phase 4D’s exact projection sum into Phase 4J’s generic Parseval theorem.

## 9. K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  target_carrier:
    H_m i

  source_carrier:
    Lp ℂ 2 (volume.restrict (Icc 0 (L_m i)))

  source_measure:
    unnormalized_Lebesgue_volume

  target_measure:
    dStar_restrict_I_m

  forward_coordinate:
    "u ↦ log(lambda_m i * u)"

  inverse_coordinate:
    "x ↦ exp x / lambda_m i"

  endpoint_relation:
    measure_equality_only

  additive_mode:
    "L_m^(-1/2) * exp(2*pi*I*n*x/L_m)"

  target_mode:
    literal_V_n_m

  inner_orientation:
    conjugate_linear_first

  coefficient_orientation:
    inner_basis_vector_then_f

  basis_target:
    HilbertBasis_Z_Complex_H_m

  first_consumer:
    exact_unweighted_modeSet_complement_Parseval

  forbidden_outputs:
    - physical_weighted_energy_bound
    - SelectedProjectionTailDecay
    - selected_residual_decay
    - compact_open_convergence
    - SlotS2
```

`[ABSTRACT][CONDITIONAL]`

## 10. Mandatory plants

### `P056T-1 — density`

Mutation:

```text
dStar.restrict (I_m i)
→ volume.restrict (I_m i).
```

Required result:

```text
G6_S2_LOG_WINDOW_COMPLETENESS_DENSITY_MISMATCH
```

The logarithmic Jacobian no longer cancels.

### `P056T-2 — endpoint convention`

Mutation:

```text
treat Icc 0 L and Ioc 0 L as pointwise-identical domains
```

or replace volume with a fixture carrying a Dirac mass at an endpoint.

Required result:

```text
G6_S2_LOG_WINDOW_COMPLETENESS_ENDPOINT_NULL_SET_MISMATCH
```

The bridge is valid because endpoints are null for volume, not because the sets are equal.

### `P056T-3 — normalized Haar versus interval volume`

Mutation:

```text
transport AddCircle.fourierBasis directly
without the L_m^(-1/2) scale.
```

Required result:

```text
G6_S2_LOG_WINDOW_COMPLETENESS_HAAR_VOLUME_NORMALIZATION_MISMATCH
```

The transported constant mode has norm squared (L_m), not one.

### `P056T-4 — mode normalization**

Mutation:

```text
L_m^(-1/2)
→ 1
```

or apply the factor twice.

Required result:

```text
G6_S2_LOG_WINDOW_COMPLETENESS_MODE_NORMALIZATION_MISMATCH
```

### `P056T-5 — inverse/surjectivity**

Mutation:

```text
ψ x = exp x
```

or:

```text
ψ x = exp x / lambda_m^2.
```

Required result:

```text
G6_S2_LOG_WINDOW_COMPLETENESS_INVERSE_COORDINATE_MISMATCH
```

The forward `Lp` map remains isometric but no longer has the claimed inverse; completeness cannot be transported.

### `P056T-6 — Fourier sign and complex orientation**

Mutation:

```text
inner ℂ (basis n) f
→ inner ℂ f (basis n)
```

or replace `n` by `-n` in only one side of the coefficient crosswalk.

Required result:

```text
G6_S2_LOG_WINDOW_COMPLETENESS_FOURIER_ORIENTATION_MISMATCH
```

### `P056T-7 — literal-family firewall**

Mutation:

```text
V_n_m i n
→ (-1)^n • V_n_m i n
```

or use an arbitrary Hilbert basis.

The mutated family may remain complete and orthonormal.

Required result:

```text
G6_S2_LOG_WINDOW_COMPLETENESS_LITERAL_V_MODE_MISMATCH
```

This is the direct **C04/C10** plant: equivalent bases are not the literal source family consumed downstream.

### `P056T-8 — no physical-energy smuggling**

Mutation: add any theorem asserting:

```text
n²-weighted source energy;
(2*pi*n/L_m)² energy;
SelectedProjectionTailDecay;
N/log(m) coupling;
uniform selected-family tail decay.
```

Required result:

```text
G6_S2_LOG_WINDOW_COMPLETENESS_PHYSICAL_ENERGY_CLAIM_SMUGGLED
```

## 11. Validation gates

Required source gates:

```text
HEAD = origin/rh_clean =
6d4dd030a0fe9724065b7f74f7da8e2cfadf331e

D0LogWindowMeasureTransport SHA-256 =
59c6d9a3a3a3c77427997665216e3ff797b9e2dc925cb63e5e9e6df0df64905b

D0KTrialStage1 SHA-256 =
c7dd206ab7979d3390a50969c71919c04582f0c1514dbb142fe1883148ce5b48

D0HilbertBasisWeightedTail SHA-256 =
24956f668098ea0a940ba50ebdd4087d7645114c8c0919a5587f35f10135643c

D0FiniteProjectionReconstruction SHA-256 =
4f19de8c695450691266171ce05b7343c5cbe16213eb71f3b40d2b119bdcaa8d
```

Required Lean gates:

```bash
lake env lean \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0LogWindowVNMCompletenessBridge.lean

lake build Q3.Proofs.RouteB.D0LogWindowVNMCompletenessBridge

lake build

bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0LogWindowVNMCompletenessBridge.lean
```

Required taint/import gates:

```text
zero sorry
zero admit
zero exact?
zero native_decide
zero declared axiom
zero opaque certificate
zero Float
zero aristotle_output import
zero ACTIVE/RequestProject import
```

Required surface:

```text
2 public definitions
3 public theorems
3 private theorems
0 private definitions
8 total declarations
```

Required axiom audit:

```text
#print axioms coeFn_logWindowL2Equiv
#print axioms V_n_m_hilbertBasis_apply
#print axioms norm_sub_coe_P_m_N_sq_eq_tsum_complement
```

Each must return exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Required infrastructure:

```text
P056T-1 through P056T-8 all fire;
all temporary plant files removed;

proof DB:
  8 declarations indexed;
  6 theorem declarations marked proven;

67/67 orchestration tests PASS;

python3 orchestrator/spine.py --strict --reason goal-close;
strict Spine PASS;

observability:
  8 sources;
  0 stale;
  numeric ZERO_COVERAGE reported separately, not called PASS;

SQLite integrity:
  knowledge.db = ok;
  aristotle_proofs.db = ok;
  observability.db = ok;

git diff --check;
exact git status report.
```

## 12. What closes and what remains open

On success, the project proves:

```text
the exact D0.1 log-window map is an L² unitary;

the literal production family V_n_m is complete;

V_n_m is a Hilbert basis, not merely an orthonormal family;

the exact P_m_N residual norm equals the coefficient mass outside modeSet.
```

`[ABSTRACT][LEAN]`

It still does not prove:

```text
weighted Fourier-energy finiteness;
a source-specific Sobolev/derivative bound;
physical bandwidth N/log(m) → infinity;
SelectedProjectionTailDecay;
SelectedTrialNormalizerBounded;
normalized residual decay;
compact-open Mellin decay;
SlotS2.
```

`[COFINAL_FAMILY][PAPER]`

The real dependency edge removed is:

```text
literal D0 orthonormal modes
  → complete source Hilbert basis
  → exact infinite complement of the finite Galerkin projection.
```

This is genuine proof progress, not wrapper progress.

## 13. Sole next analytic node

Not authorized in this batch:

```text
G6_S2_D0_SELECTED_PHYSICAL_FOURIER_ENERGY_CONTROL
```

Its job is to define and control an independently source-grounded energy such as

[
\sum_{n\in\mathbb Z}
\left|\frac{2\pi n}{L_m}\right|^{2r}
|\langle V_{n,m},g_m\rangle|^2
]

and combine it with a non-tautological physical-bandwidth or coupled-rate law.

It must not use `SelectedProjectionTailDecay` as a premise under a new name.

## STRONGEST ATTACK

The strongest reviewer objection is:

> The source says there is a unitary, and the forward measure map compiles. Why not directly map Mathlib’s circle Fourier basis and declare victory?

Because Mathlib’s circle basis is normalized for Haar mass one, while the source interval uses Lebesgue mass (L_m). Direct transport without an explicit measure-scaling equivalence produces the wrong mode normalization.

The repaired transaction avoids that error:

```text
exact public source unitary;
exact interval Parseval;
exact normalized literal modes;
HilbertBasis.mkOfOrthogonalEqBot.
```

The second objection is:

> Completeness of a phase-twisted family would be enough abstractly. Why insist on literal equality?

Because downstream projection coefficients, `rawFplus`, and the residual crosswalk are defined using the exact `V_n_m` row and the exact `inner(V_n,f)` orientation. An equivalent basis changes those coefficients. This is not cosmetic; it is the C04/C10 same-object firewall.

## META CLOSEOUT

**What became smaller?**

```text
“prove V_n_m completeness”
```

is reduced to:

```text
forward measure push;
inverse measure push;
a.e. inverse Lp equivalence;
one coefficient normalization;
interval Parseval.
```

**What was killed?**

* direct unscaled transport of `AddCircle.fourierBasis`;
* orthonormality as a substitute for completeness;
* completeness as an unsupported source field;
* an arbitrary equivalent Hilbert basis;
* postponing the exact unweighted residual identity to another boundary.

**What must not be tried again?**

Do not identify normalized Haar with interval volume. Do not call an isometric embedding surjective until the inverse composition has been proved almost everywhere.

**Current smallest named gap:**

```text
G6_S2_D0_LOG_WINDOW_V_N_M_COMPLETENESS_BRIDGE_MISSING
```

**Next cheapest decisive test:**

Compile the inverse `Lp` composition identities and fire the normalized-Haar/interval-volume plant before attempting the Hilbert-basis constructor.

**Registered prediction:**

```text
P056T-A:
  the repaired unitary-plus-Parseval transaction closes in one production file.

P056T-B:
  the main Lean friction is inverse measure transport and endpoint measure
  normalization, not Fourier analysis.

P056T-C:
  the literal basis-value theorem closes by the pinned
  coe_mkOfOrthogonalEqBot simp law once totality is proved.

P056T-D:
  physical weighted-energy control remains independent after completeness.
```

**Fate of prior predictions:**

```text
Phase4J:
  the next source-specific wall is literal V_n_m completeness.
  CONFIRMED.

Phase4K scratch:
  the forward logarithmic measure map is executable.
  CONFIRMED AS FORWARD MAP ONLY.

Original Candidate A:
  direct basis transport is clean without further normalization work.
  REFUTED; repaired by interval Parseval totality.

Candidate C:
  completeness can be placed in source data.
  KILLED BY C09/C10.
```

```yaml
iteration:
  target: literal_V_n_m_completeness
  status: OPEN
  failed_strategy: direct_transport_of_normalized_Haar_fourierBasis_to_unnormalized_interval
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: G6_S2_D0_LOG_WINDOW_V_N_M_COMPLETENESS_BRIDGE_MISSING
  invariant_learned: measure_normalization_endpoint_null_sets_and_literal_basis_values_must_survive_transport
  forbidden_future_move: postulate_completeness_or_use_an_equivalent_nonliteral_basis
  next_decisive_test: inverse_Lp_equivalence_plus_Haar_volume_normalization_plant
  progress_class: PROOF_PROGRESS
  route_score: 5
```

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS:
  TRY_G6_S2_D0_LOG_WINDOW_V_N_M_COMPLETENESS_BRIDGE

TRANSACTION:
  G6_S2_D0_LOG_WINDOW_V_N_M_COMPLETENESS_BRIDGE

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
  expected_head: 6d4dd030a0fe9724065b7f74f7da8e2cfadf331e

  required_sha256:
    q3.lean.aristotle/Q3/Proofs/RouteB/D0LogWindowMeasureTransport.lean:
      59c6d9a3a3a3c77427997665216e3ff797b9e2dc925cb63e5e9e6df0df64905b
    q3.lean.aristotle/Q3/Proofs/RouteB/D0KTrialStage1.lean:
      c7dd206ab7979d3390a50969c71919c04582f0c1514dbb142fe1883148ce5b48
    q3.lean.aristotle/Q3/Proofs/RouteB/D0HilbertBasisWeightedTail.lean:
      24956f668098ea0a940ba50ebdd4087d7645114c8c0919a5587f35f10135643c
    q3.lean.aristotle/Q3/Proofs/RouteB/D0FiniteProjectionReconstruction.lean:
      4f19de8c695450691266171ce05b7343c5cbe16213eb71f3b40d2b119bdcaa8d
    q3.lean.aristotle/docs/INSIGHTS.md:
      f46fb47fc5cab9452d87e7afee06b89edbf7f592396c3ced80a982390f6e0341

ON_SOURCE_MISMATCH:
  stop: G6_S2_LOG_WINDOW_COMPLETENESS_SOURCE_LOCK_MISMATCH
  edit_files: false

CREATE:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0LogWindowVNMCompletenessBridge.lean

IMPORTS_EXACT:
  - Q3.Proofs.RouteB.D0FiniteProjectionReconstruction
  - Q3.Proofs.RouteB.D0HilbertBasisWeightedTail
  - Mathlib.Analysis.Fourier.AddCircle
  - Mathlib.MeasureTheory.Function.Jacobian

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE:
  definitions: 2
  theorems: 3
  private_theorems: 3
  private_definitions: 0

PRIVATE_THEOREMS:
  - logWindow_measurePreserving
  - expWindow_measurePreserving
  - V_n_m_span_orthogonal_eq_bot

PUBLIC_DEFINITION_1: |
  noncomputable def logWindowL2Equiv (i : PairIndex) :
      MeasureTheory.Lp ℂ 2
          (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))
        ≃ₗᵢ[ℂ]
      H_m i := by
    ...

PUBLIC_THEOREM_1: |
  theorem coeFn_logWindowL2Equiv
      (i : PairIndex)
      (f : MeasureTheory.Lp ℂ 2
        (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))) :
      ((logWindowL2Equiv i f : H_m i) : ℝ → ℂ)
        =ᵐ[dStar.restrict (I_m i)]
          (fun u : ℝ =>
            f (Real.log (lambda_m i * u))) := by
    ...

PUBLIC_DEFINITION_2: |
  noncomputable def V_n_m_hilbertBasis (i : PairIndex) :
      HilbertBasis ℤ ℂ (H_m i) :=
    HilbertBasis.mkOfOrthogonalEqBot
      (V_n_m_orthonormal i)
      (V_n_m_span_orthogonal_eq_bot i)

PUBLIC_THEOREM_2: |
  @[simp] theorem V_n_m_hilbertBasis_apply
      (i : PairIndex) (n : ℤ) :
      V_n_m_hilbertBasis i n = V_n_m i n := by
    simp [V_n_m_hilbertBasis]

PUBLIC_THEOREM_3: |
  theorem norm_sub_coe_P_m_N_sq_eq_tsum_complement
      (i : PairIndex) (f : H_m i) :
      ‖f - (P_m_N i f : H_m i)‖ ^ 2 =
        ∑' n : ℤ,
          if n ∈ modeSet i then 0
          else ‖inner ℂ (V_n_m i n) f‖ ^ 2 := by
    rw [coe_P_m_N_apply_eq_sum_inner_V_n_m_smul]
    simpa [V_n_m_hilbertBasis_apply] using
      norm_sub_basisPartialSum_sq_eq_tsum
        (V_n_m_hilbertBasis i)
        (modeSet i)
        f

REQUIRED_PROOF_ROUTE:
  - prove exact forward logarithmic measure preservation with the Jacobian theorem
  - derive reverse measure preservation using the forward map and a.e. inverse identities
  - construct the Lp equivalence with compMeasurePreserving_l_i and ofLinearIsometry
  - expose only an a.e. representative theorem
  - prove Icc/Ioc restricted-volume equality from endpoint atomlessness
  - prove inner(U_n,g) = sqrt(L_m) * fourierCoeffOn g n
  - apply hasSum_sq_fourierCoeffOn to kill the orthogonal complement
  - construct HilbertBasis with mkOfOrthogonalEqBot
  - prove literal equality to V_n_m
  - consume Phase4D and Phase4J for the unweighted complement theorem

FORBIDDEN_PROOF_ROUTE:
  - direct unscaled transport of AddCircle.fourierBasis
  - identify normalized Haar with ordinary interval volume
  - assert pointwise equality of arbitrary Lp representatives
  - prove only an isometric embedding without surjectivity
  - construct an arbitrary or phase-twisted equivalent basis
  - add completeness as source data
  - choose an n_squared or physical-frequency weight
  - prove SelectedProjectionTailDecay
  - prove selected residual decay
  - prove compact-open convergence
  - prove SlotS2

K6_OBJECT_PRECOMMIT:
  source_measure: volume_restrict_Icc_0_L
  target_measure: dStar_restrict_I_m
  forward_map: log_lambda_mul_u
  inverse_map: exp_x_div_lambda
  endpoint_relation: ae_measure_only
  mode_normalization: sqrt_L_inverse
  mode_phase: plus_2pi_I_n_x_div_L
  coefficient_orientation: inner_basis_f
  basis_values: literal_V_n_m
  first_consumer: unweighted_modeSet_complement_Parseval

MANDATORY_PLANTS:
  P056T_1_DENSITY:
    expected: G6_S2_LOG_WINDOW_COMPLETENESS_DENSITY_MISMATCH

  P056T_2_ENDPOINT:
    expected: G6_S2_LOG_WINDOW_COMPLETENESS_ENDPOINT_NULL_SET_MISMATCH

  P056T_3_HAAR_VOLUME:
    expected: G6_S2_LOG_WINDOW_COMPLETENESS_HAAR_VOLUME_NORMALIZATION_MISMATCH

  P056T_4_MODE_NORMALIZATION:
    expected: G6_S2_LOG_WINDOW_COMPLETENESS_MODE_NORMALIZATION_MISMATCH

  P056T_5_INVERSE:
    expected: G6_S2_LOG_WINDOW_COMPLETENESS_INVERSE_COORDINATE_MISMATCH

  P056T_6_FOURIER_ORIENTATION:
    expected: G6_S2_LOG_WINDOW_COMPLETENESS_FOURIER_ORIENTATION_MISMATCH

  P056T_7_LITERAL_FAMILY:
    expected: G6_S2_LOG_WINDOW_COMPLETENESS_LITERAL_V_MODE_MISMATCH

  P056T_8_NO_PHYSICAL_ENERGY:
    expected: G6_S2_LOG_WINDOW_COMPLETENESS_PHYSICAL_ENERGY_CLAIM_SMUGGLED

VALIDATION:
  - verify HEAD equals origin before editing
  - verify all five SHA-256 locks
  - direct Lean on D0LogWindowVNMCompletenessBridge.lean
  - dedicated module build
  - full build
  - q3_check PASS
  - taint and forbidden-import scan
  - exact public surface 2_definitions_3_theorems_3_private_theorems
  - fire P056T_1 through P056T_8
  - remove all temporary plant files
  - print axioms for all three public theorems
  - require exactly [propext, Classical.choice, Quot.sound]
  - proof database reimport
  - require 8 declarations indexed and 6 theorem declarations proven
  - run all 67 orchestration tests
  - run python3 orchestrator/spine.py --strict --reason goal-close
  - require strict Spine PASS
  - report observability as 8_sources_0_stale
  - report numeric ZERO_COVERAGE separately
  - run SQLite integrity_check on all three databases
  - require all three equal ok
  - git diff --check
  - exact git status report

STOP:
  G6_S2_D0_LOG_WINDOW_V_N_M_COMPLETENESS_BRIDGE_MISSING

SUCCESS:
  G6_S2_D0_LOG_WINDOW_V_N_M_HILBERT_BASIS_AND_COMPLEMENT_PARSEVAL_PROVED

FAILURE_CODES:
  - G6_S2_LOG_WINDOW_COMPLETENESS_SOURCE_LOCK_MISMATCH
  - G6_S2_LOG_WINDOW_FORWARD_MEASURE_MAP_GAP
  - G6_S2_LOG_WINDOW_INVERSE_MEASURE_MAP_GAP
  - G6_S2_LOG_WINDOW_LP_EQUIV_INVERSE_GAP
  - G6_S2_LOG_WINDOW_ENDPOINT_NULL_SET_GAP
  - G6_S2_LOG_WINDOW_HAAR_VOLUME_NORMALIZATION_MISMATCH
  - G6_S2_LOG_WINDOW_FOURIER_COEFFICIENT_ORIENTATION_MISMATCH
  - G6_S2_LOG_WINDOW_LITERAL_V_MODE_BASIS_MISMATCH
  - G6_S2_LOG_WINDOW_COMPLETENESS_PUBLIC_SURFACE_MISMATCH
  - G6_S2_LOG_WINDOW_COMPLETENESS_PLANT_INERT
  - LEAN_BUILD_FAIL

SOLE_NEXT_NODE_NOT_AUTHORIZED:
  name: G6_S2_D0_SELECTED_PHYSICAL_FOURIER_ENERGY_CONTROL
  purpose: >-
    define and bound a source-grounded physical Fourier energy with
    frequency 2*pi*n/L_m and a separate coupled schedule law

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
