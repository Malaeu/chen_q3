# PROSHKA REQUEST — Goal 057 B3.0C source archimedean mode-pairing integrability release

## 0. Requested decision

Return exactly one primary operational verdict for the smallest next atom
after the proved B3.0B3 transaction:

`GOAL057_B3_0C_SOURCE_ARCH_MULTIPLIER_MODE_PAIRING_INTEGRABILITY`

Candidate A is:

`TRY_GOAL057_B3_0C_SOURCE_ARCH_MULTIPLIER_MODE_PAIRING_INTEGRABILITY`

If Candidate A is source-faithful and minimal, release it with an exact Lean
contract and mandatory plants.  If it is not, return one `KILL_` or `WALL_`
code naming the first missing source fact and the smallest repaired atom.

This is one `DELEGATED_STRATEGIC_REVIEW` in the same living Goal 057 phase and
same living conversation.  It is not an owner boundary.

## 1. Immutable control state

```yaml
repo: /Users/emalam/GitHub/rh_lean_01_2026
branch: rh_clean
head: 17e0ffc9424a726eda25f20039d8949ac95e1adb
active_goal: 057
route: CHALLENGER_NOT_RH
bus_010: VOID
goal_055: HOLD
g2_ccm: FROZEN
aristotle_submission: NONE
route_promotion: false
px_rh_claim: NOT_MADE
owner_gate: PX_RH_CLAIM_ONLY
coarse_checkpoints_closed: 0
coarse_checkpoints_remaining: 10
current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
```

Do not create Bus 010, decrement the ten-checkpoint ledger, invoke H4a1b,
promote Route B, or claim RH.

## 2. Closed parent facts

### B3.0B1 — envelope-weighted fixed-mode L2

Production file:

`Q3/Proofs/RouteB/D0PstarVModeLogWeightedL2.lean`

SHA-256:

`beb6f951a5b3db4a0b234137a61e9968696f77ba53393419fabdeed239262c87`

It proves:

```lean
theorem vModeLogGrowthEnvelope_mul_fourier_logWindowZeroExtendedMode_memLp
    (i : PairIndex) (n : ℤ) :
    MemLp
      (fun t : ℝ =>
        (vModeLogGrowthEnvelope t : ℂ) *
          𝓕 (logWindowZeroExtendedMode i n) t)
      2 volume
```

with

```lean
def vModeLogGrowthEnvelope (t : ℝ) : ℝ :=
  1 + Real.log (2 + |t|)
```

and hence pointwise `1 ≤ vModeLogGrowthEnvelope t`.

### B3.0B2 — exact source symbol

`sourceArchimedeanMultiplier` is the exact source multiplier in Mathlib's
cycles-per-unit Fourier coordinate, with the source angular coordinate scaled
by `2*pi`.  Its global absolute domination is production-proved.

### B3.0B3 — exact-symbol weighted fixed-mode L2

Production file:

`Q3/Proofs/RouteB/D0PstarExactArchSymbolWeightedModeL2.lean`

SHA-256:

`99b7ad19089b17a0cde4492a239c4b5b8a5b8e8ea8c6b6aa2cc348c8324200d7`

Exact public theorem:

```lean
theorem sourceArchimedeanMultiplier_mul_fourier_logWindowZeroExtendedMode_memLp
    (i : PairIndex) (n : ℤ) :
    MemLp
      (fun t : ℝ =>
        (sourceArchimedeanMultiplier t : ℂ) *
          𝓕 (logWindowZeroExtendedMode i n) t)
      2 volume
```

It passed direct Lean, target build 7,762, full build 7,817, `q3_check`, 80/80
unit tests, strict Spine, 8/8 plants, 3/3 proof-DB declarations, and standard
axioms only.  Parent B3.0B is closed.  B3.0 remains open.

## 3. Primary-source orientation lock

Source-lock file:

`ACTIVE/requests/routeB_lamport_rh_closure/D0_2_EXACT_WEIL_SESQUILINEAR_FORM.md`

SHA-256:

`52c58cee35344edc5baa30f3e2028b402c9a64a0e9a08c4dd093557a5a561308`

It fixes:

```text
QW(f,g) = Psi(f^* * g)
```

and explicitly states that `BW_m` is antilinear in the first variable and
linear in the second.  Its coefficient expansion is

```text
BW_m_N(f,g) = sum_(r,s) conjugate(c_r) tau_(r,s) d_s.
```

Therefore the candidate pairing must conjugate the first Fourier mode:

```text
conj(Fourier(V_n)) * sourceArchSymbol * Fourier(V_r).
```

Reversing the conjugation is not a harmless renaming.

## 4. Proposed exact public contract

Owned production file, if released:

`Q3/Proofs/RouteB/D0PstarSourceArchModePairingIntegrable.lean`

Proposed exact import:

```lean
import Q3.Proofs.RouteB.D0PstarExactArchSymbolWeightedModeL2
```

Proposed public surface: exactly one theorem, zero public definitions, zero
structures.

```lean
open scoped ComplexConjugate

theorem sourceArchimedeanModePairing_integrable
    (i : PairIndex) (n r : ℤ) :
    Integrable
      (fun t : ℝ =>
        conj (𝓕 (logWindowZeroExtendedMode i n) t) *
          (sourceArchimedeanMultiplier t : ℂ) *
          𝓕 (logWindowZeroExtendedMode i r) t)
```

No integral value, symmetry, matrix entry, source form, operator graph,
domain membership, or uniform mode bound is claimed.

## 5. Lean-compiled scratch evidence

Scratch path outside the repository:

`/tmp/Goal057B3_0C_Scratch.lean`

SHA-256:

`b9982a75e5258b556474353ec5ad2a849b465f23d223d9564cfc78a68e173e5e`

Size: 2,251 bytes / 57 lines.

Direct command:

```text
lake env lean /tmp/Goal057B3_0C_Scratch.lean
```

Result: PASS under the production toolchain.

The compiled proof uses exactly this mathematical chain:

1. Deduce the unweighted Fourier mode is in `L²` from B3.0B1 by
   `MemLp.of_le` and `1 ≤ vModeLogGrowthEnvelope`; do not divide by the exact
   source symbol.
2. Prove the Fourier transform is strongly measurable from the integrability
   of the compactly supported zero-extension and
   `VectorFourier.fourierIntegral_continuous`.
3. Preserve `MemLp 2` under first-factor conjugation using
   `MemLp.congr_norm` and `norm_conj`.
4. Use the production B3.0B3 theorem for the exact-symbol-weighted `r` mode.
5. Apply Mathlib's `MemLp.integrable_mul`, i.e. Hölder `L²×L²→L¹`.

The scratch exposed and resolved the pinned conjugation syntax:
`open scoped ComplexConjugate` is required; `Complex.conj` is not the
identifier in this toolchain.

## 6. Why this is the smallest honest next atom

- It is the first source-shaped cross-mode sesquilinear carrier.
- It preserves the source's antilinear-first convention.
- It consumes only already-proved fixed-mode facts.
- It does not manufacture the missing prime and pole components.
- It does not equate a form-domain fact with an associated-operator-domain
  fact.
- It does not promote a fixed `(i,n,r)` theorem to uniform/cofinal control.

The larger next wall after this atom remains:

`SOURCE_WEIL_FORM_FOURIER_MULTIPLIER_DECOMPOSITION`

followed by source-locked pole/prime action and the associated graph.

## 7. Proposed private support budget

Allow at most three private theorems:

1. `logWindowZeroExtendedMode_integrable_for_pairing`
2. `fourier_logWindowZeroExtendedMode_memLp_two`
3. `conj_fourier_logWindowZeroExtendedMode_memLp_two`

If you can reduce that private surface without hiding a source premise, do so.
Do not add an abstract structure or a premise-only wrapper.

## 8. Mandatory plants

Return exact mutations and stop codes, at minimum covering:

1. `P057_B3_0C_1_CONJUGATION_ORIENTATION`
   - mutate by conjugating the second mode or deleting conjugation;
   - required code: `SOURCE_FORM_ANTILINEAR_FIRST_ORIENTATION_MISMATCH`.
2. `P057_B3_0C_2_DIVIDE_BY_SOURCE_SYMBOL`
   - derive the left `L²` factor by dividing by
     `sourceArchimedeanMultiplier`;
   - required code: `SOURCE_SYMBOL_NONVANISHING_NOT_PROVED`.
3. `P057_B3_0C_3_L2_PRODUCT_AS_L2`
   - claim the product is still `MemLp 2` instead of `Integrable`;
   - required code: `HOLDER_EXPONENT_TARGET_MISMATCH`.
4. `P057_B3_0C_4_FIXED_TO_UNIFORM`
   - promote fixed `(n,r)` integrability to a uniform cofinal estimate;
   - required code: `UNIFORM_COFINAL_MODE_BOUND_MISSING`.
5. `P057_B3_0C_5_PAIRING_AS_SOURCE_FORM`
   - present the archimedean integrand as the full source Weil form;
   - required code: `SOURCE_WEIL_FORM_DECOMPOSITION_MISSING`.
6. `P057_B3_0C_6_FORM_TO_OPERATOR_GRAPH`
   - treat integrability as associated-operator graph/domain membership;
   - required code: `FORM_DOMAIN_NOT_OPERATOR_DOMAIN`.
7. `P057_B3_0C_7_GENERATED_BACKEND_IMPORT`
   - inject any generated PSD/Step33/hbox/payload supplier;
   - required code: `ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK`.
8. `P057_B3_0C_8_MODE_INDEX_ORIENTATION`
   - swap `n,r` without the corresponding conjugation/source convention;
   - required code: `SOURCE_MODE_PAIRING_INDEX_ORIENTATION_MISMATCH`.

All mutation artifacts must stay outside production and be removed after
testing.

## 9. Required response schema

```yaml
STATUS: OPEN
PRIMARY: TRY_|KILL_|WALL_
RELEASED_ATOM:
OWNED_FILE:
EXACT_IMPORTS:
EXACT_PUBLIC_THEOREMS:
PRIVATE_SUPPORT_BUDGET:
SUCCESS_CODE:
STOP_CODE:
PLANTS:
PARENT_AFTER_SUCCESS:
NEXT_GAP_AFTER_SUCCESS:
COARSE_CHECKPOINTS_CLOSED_AFTER_SUCCESS: 0
COARSE_CHECKPOINTS_REMAINING_AFTER_SUCCESS: 10
PHASE_KEY_CHANGE: false
NEW_CHAT: false
OWNER_AUTHORITY_REQUIRED: false
```

Then give:

1. source-faithfulness check for the conjugation and mode-index orientation;
2. minimal Lean proof plan using the pinned API;
3. the strongest attack against route progress;
4. exact semantic boundary after success;
5. the smallest next atom, without authorizing it unless separately stated.

## 10. Boundary

This request authorizes no Lean edit by itself.  Codex may create the owned
production file only if you return an operative `TRY_` release.  The sole
owner gate remains `PX_RH_CLAIM`; promotion and any RH statement remain
forbidden.
