# Public RH Export Index and Axiom Receipt v1

```yaml
document_class: PUBLIC_EXPORT_RECEIPT
version: 1
status: AUDITED_BASELINE
audited_at: 2026-08-27
audited_baseline_head: 49c3b916cfa24df9ba6b49b9d9952a0cf06d3da9
audited_baseline_scope: LEAN_PUBLIC_EXPORTS
branch: rh_clean
unconditional_rh_proof: false
default_target: Q3
default_target_class: CONDITIONAL_COMPILED
route_b: CHALLENGER_NOT_RH
```

This receipt records what the named Lean declarations state and which axioms
Lean reports for them at the pinned baseline. It does not certify the truth of
project axioms or turn an explicit mathematical premise into a proved premise.

## Classification vocabulary

- `CORE_SHARED`: definitions used by more than one route.
- `PUBLIC_CANONICAL`: honest public interface with all hard mathematical inputs
  explicit in its theorem type.
- `CHALLENGER`: conditional research route that is not a public RH result.
- `CONDITIONAL_COMPILED`: compiled declaration whose proof depends on project
  axioms or a legacy conditional route.
- `LEGACY`: retained historical or compatibility surface; not a public result.
- `EXPERIMENT`: noncanonical exploratory surface.
- `ARCHIVE`: historical material outside the live interface.

## Default entrypoint

The Lake default target is `Q3`, rooted at `q3.lean.aristotle/Q3.lean`. It
imports both the corrected square-class interfaces and the compiled broad-cone
route:

```text
Q3.Basic.WeilSquareClass       PUBLIC_CANONICAL_CANDIDATE module
Q3.Basic.WeilDirectRoute      PUBLIC_CANONICAL_CANDIDATE module
Q3.Axioms                     CONDITIONAL_COMPILED
Q3.Main                       CONDITIONAL_COMPILED
```

Therefore the default target is `CONDITIONAL_COMPILED`; it is not yet a clean
canonical public slice.

```yaml
classification_granularity:
  corrected_theorems: DECLARATION_LEVEL_PUBLIC_CANONICAL_INTERFACES
  corrected_modules: PUBLIC_CANONICAL_CANDIDATES
  module_firewall_status: BLOCKED_BY_MIXED_Q3_BASIC_DEFS
  canonical_public_entrypoint_established: false
```

## Shared RH object

Source: `q3.lean.aristotle/Q3/Basic/Defs.lean:177`

```lean
def RH : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1/2
```

The source object is Mathlib's `riemannZeta`.

## Corrected square-class interfaces

### `Q3.RH_of_global_weil_positivity`

Source: `q3.lean.aristotle/Q3/Basic/WeilDirectRoute.lean:63`

```lean
theorem RH_of_global_weil_positivity
    (hcriterion : ExactWeilCriterion)
    (hpositive : GlobalWeilPositivity) :
    RH
```

- Test class: `Q3.W_sq`.
- Source object: `Q3.WeilForm`, definitionally `Q3.Q` on the square class.
- Classification: `PUBLIC_CANONICAL` interface.
- Status: conditional; both hard mathematical inputs are explicit.

Exact receipt:

```text
'Q3.RH_of_global_weil_positivity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `Q3.RH_of_weil_geometric_sign_replacement`

Source: `q3.lean.aristotle/Q3/Basic/WeilDirectRoute.lean:78`

```lean
theorem RH_of_weil_geometric_sign_replacement
    (hcriterion : ExactWeilCriterion)
    (hsign : WeilGeometricSignReplacement) :
    RH
```

- Test class: `Q3.W_sq`.
- Source object: `Q3.WeilForm`.
- Classification: `PUBLIC_CANONICAL` interface.
- Status: conditional; the sign replacement is an explicit input.

Exact receipt:

```text
'Q3.RH_of_weil_geometric_sign_replacement' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Compiled broad-cone exports

These declarations end in the same `Q3.RH` type as the corrected interfaces,
but consume the broad pointwise-nonnegative class `Q3.Weil_cone`, not
`Q3.W_sq`. They are `CONDITIONAL_COMPILED`.

| Declaration | Source | Exact statement |
|---|---|---|
| `Q3.Proofs.PaperMainlineAtomRoute.RH_of_shifted_atom_route` | `q3.lean.aristotle/Q3/Proofs/PaperMainlineAtomRoute.lean:67` | `Q3.RH` |
| `Q3.RH_of_shifted_atom_route` | `q3.lean.aristotle/Q3/Proofs/PaperMainlineAtomRoute.lean:81` | `Q3.RH` |
| `Q3.Main.RH_of_Weil_and_Q3` | `q3.lean.aristotle/Q3/Main.lean:49` | `Q3.RH` |
| `Q3.MainTheorems.RH_proven` | `q3.lean.aristotle/Q3/MainTheorems.lean:53` | `Q3.RH` |
| `Q3.MainTheorems.RH_proven` | `q3.lean.aristotle/MainTheorems.lean:46` | `Q3.RH` |

Exact receipt for the compiled wrappers:

```text
'Q3.Main.RH_of_Weil_and_Q3' depends on axioms: [propext,
 Classical.choice,
 Q3.Weil_criterion,
 Q3.prime_term_le_at_t_critical_axiom,
 Quot.sound]
'Q3.RH_of_shifted_atom_route' depends on axioms: [propext,
 Classical.choice,
 Q3.Weil_criterion,
 Q3.prime_term_le_at_t_critical_axiom,
 Quot.sound]
'Q3.MainTheorems.RH_proven' depends on axioms: [propext,
 Classical.choice,
 Q3.Weil_criterion,
 Q3.prime_term_le_at_t_critical_axiom,
 Quot.sound]
```

### Broad-cone positivity exports

```yaml
broad_cone_positivity_exports:
  declarations:
    - Q3.Proofs.PaperMainlineAtomRoute.Q_nonneg_on_Weil_cone_current_atom_route
    - Q3.Q_nonneg_on_Weil_cone_current_atom_route
    - Q3.Main.Q_nonneg_on_Weil_cone
    - Q3.MainTheorems.Q_nonneg_Weil_cone@root_MainTheorems
  classification: CONDITIONAL_COMPILED
  test_class: Q3.Weil_cone
  source_object: Q3.Q
```

| Declaration | Source | Exact statement |
|---|---|---|
| `Q3.Proofs.PaperMainlineAtomRoute.Q_nonneg_on_Weil_cone_current_atom_route` | `q3.lean.aristotle/Q3/Proofs/PaperMainlineAtomRoute.lean:51` | `∀ Φ ∈ Q3.Weil_cone, Q3.Q Φ ≥ 0` |
| `Q3.Q_nonneg_on_Weil_cone_current_atom_route` | `q3.lean.aristotle/Q3/Proofs/PaperMainlineAtomRoute.lean:76` | `∀ Φ ∈ Q3.Weil_cone, Q3.Q Φ ≥ 0` |
| `Q3.Main.Q_nonneg_on_Weil_cone` | `q3.lean.aristotle/Q3/Main.lean:39` | `∀ Φ ∈ Q3.Weil_cone, Q3.Q Φ ≥ 0` |
| `Q3.MainTheorems.Q_nonneg_Weil_cone` | `q3.lean.aristotle/MainTheorems.lean:42` | `∀ Φ ∈ Q3.Weil_cone, Q3.Q Φ ≥ 0` |

Exact receipts:

```text
'Q3.Proofs.PaperMainlineAtomRoute.Q_nonneg_on_Weil_cone_current_atom_route' depends on axioms: [propext,
 Classical.choice,
 Q3.prime_term_le_at_t_critical_axiom,
 Quot.sound]
'Q3.Q_nonneg_on_Weil_cone_current_atom_route' depends on axioms: [propext,
 Classical.choice,
 Q3.prime_term_le_at_t_critical_axiom,
 Quot.sound]
'Q3.Main.Q_nonneg_on_Weil_cone' depends on axioms: [propext,
 Classical.choice,
 Q3.prime_term_le_at_t_critical_axiom,
 Quot.sound]
'Q3.MainTheorems.Q_nonneg_Weil_cone' depends on axioms: [propext,
 Classical.choice,
 Q3.prime_term_le_at_t_critical_axiom,
 Quot.sound]
```

The internal RH wrapper has the full broad-cone RH profile:

```text
'Q3.Proofs.PaperMainlineAtomRoute.RH_of_shifted_atom_route' depends on axioms: [propext,
 Classical.choice,
 Q3.Weil_criterion,
 Q3.prime_term_le_at_t_critical_axiom,
 Quot.sound]
```

The two `MainTheorems.lean` files define the same fully qualified declaration
with different proof terms. They are not byte-identical sources:

```yaml
collision: DUPLICATE_FQNAME_DIFFERENT_PROOF_SURFACES
surface_1: q3.lean.aristotle/Q3/MainTheorems.lean
surface_1_sha256: 38587ad3a461d1ff2590d040f78ab256bf1a08247930a3e54eb17c73f5774e67
surface_2: q3.lean.aristotle/MainTheorems.lean
surface_2_sha256: 592a371009a9c881233d33f38f1ccb42dc1c8a06202bcc78662c54d6ed82b732
```

The two `Q3.MainTheorems.RH_proven` surfaces were checked in separate Lean
invocations. Both produced the identical displayed axiom profile; they remain
distinct proof surfaces and are not imported together.

## Broken clean surface

Declaration: `Q3.Clean.RH_proven_clean`  
Source: `q3.lean.aristotle/Q3/Clean/MainClean.lean:48`  
Classification: `LEGACY`

The source states `Q3.RH` and contains `sorry` at line 59. The targeted build
`lake build Q3.Clean.MainClean` fails in `Q3.Clean.TheoremsTier2`; therefore an
exact `#print axioms Q3.Clean.RH_proven_clean` receipt is unavailable.

```yaml
exact_axiom_receipt: UNAVAILABLE_BUILD_FAILED
failure_code: CLEAN_TIER2_UNKNOWN_IDENTIFIERS
test_class: Q3.Weil_cone
source_object: Q3.Q
criterion: Q3.Clean.Weil_criterion
criterion_verifier: AXIOM
classification: LEGACY
build_status: FAILED
confirmed_partial_receipt:
  declaration: Q3.Clean.Theorems.off_diag_exp_sum
  axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The failure includes unresolved identifiers in `OffDiagBridgeV3`,
`QNonnegBridgeV2`, and `A1DensityBridgeV2`. This surface must not be presented
as canonical or as a compiled RH result.

## Route B challenger interfaces

These modules are not imported by the default `Q3` root. They are classified
as `CHALLENGER`; their theorem types expose the unclosed slots.

Source: `q3.lean.aristotle/Q3/Proofs/RouteB/ClassicalXiInterface.lean:108`

```lean
theorem rh_iff_centeredXi_zeros_real :
    Q3.RH ↔ CenteredXiZerosReal
```

Source: `q3.lean.aristotle/Q3/Proofs/RouteB/CanonicalRHRouteSkeleton.lean:145`

```lean
theorem rh_of_canonical_strip_slots
    {Index : Type*} (C : CanonicalApproximation Index)
    (H2aAt S1At : Index → Prop) (anchor : ℂ)
    (hH1 : SlotH1 C)
    (hH2a : SlotH2a C H2aAt)
    (hanchor : SlotAnchor C anchor)
    (hS1 : SlotS1 C S1At)
    (hMontel : MontelAnchorGate C H2aAt S1At anchor)
    (h510 : Theorem510RealZeroBridge C H2aAt)
    (hS2 : SlotS2 C) :
    Q3.RH
```

Source: `q3.lean.aristotle/Q3/Proofs/RouteB/CanonicalRHRouteSkeleton.lean:177`

```lean
theorem rh_of_canonical_slots
    {Index : Type*} (C : CanonicalApproximation Index)
    (H2aAt S1At : Index → Prop) (anchor : ℂ)
    (hH1 : SlotH1 C)
    (hH2a : SlotH2a C H2aAt)
    (hanchor : SlotAnchor C anchor)
    (hS1 : SlotS1 C S1At)
    (hMontel : MontelAnchorGate C H2aAt S1At anchor)
    (h510 : Theorem510RealZeroBridge C H2aAt)
    (hS2 : SlotS2 C) :
    Q3.RH
```

```yaml
route_b_source_objects:
  Q3.RouteB.rh_iff_centeredXi_zeros_real:
    test_class: NOT_APPLICABLE
    source_objects:
      - Q3.RouteB.centeredXi
      - Q3.RouteB.CenteredXiZerosReal
      - Q3.RouteB.centeredCriticalStrip
  Q3.RouteB.CanonicalRHRoute.rh_of_canonical_strip_slots:
    test_class: NOT_APPLICABLE
    source_objects:
      - Q3.RouteB.CanonicalRHRoute.selectedFamily
      - Q3.RouteB.CanonicalRHRoute.SlotS2
      - Q3.RouteB.centeredXi
  Q3.RouteB.CanonicalRHRoute.rh_of_canonical_slots:
    test_class: NOT_APPLICABLE
    source_objects:
      - Q3.RouteB.CanonicalRHRoute.selectedFamily
      - Q3.RouteB.CanonicalRHRoute.SlotS2
      - Q3.RouteB.centeredXi
```

Exact receipts:

```text
'Q3.RouteB.rh_iff_centeredXi_zeros_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.CanonicalRHRoute.rh_of_canonical_strip_slots' depends on axioms: [propext, Classical.choice, Quot.sound]
'Q3.RouteB.CanonicalRHRoute.rh_of_canonical_slots' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Standard Lean axioms in these receipts do not close the explicit mathematical
slots. Route B remains challenger / not RH.

## Test-class crosswalk

```yaml
broad_legacy:
  test_class: Q3.Weil_cone
  shape: even_and_pointwise_nonnegative_and_compactly_supported_and_continuous
  source_object: Q3.Q
  criterion: Q3.Weil_criterion
  criterion_verifier: AXIOM

corrected:
  local_test_class: Q3.W_sq_K
  global_test_class: Q3.W_sq
  shape: nonempty_WeilSquareWitness
  source_object: Q3.WeilForm
  criterion: Q3.ExactWeilCriterion
  criterion_verifier: EXPLICIT_PROP_INPUT
```

The common codomain `Q3.RH` is not a valid classifier. The theorem's premise
and exact test class determine whether it belongs to the corrected or legacy
route.

## Forward dependency graph

```text
Q3.Main.RH_of_Weil_and_Q3
→ Q3.RH_of_shifted_atom_route
→ Q3.Proofs.PaperMainlineAtomRoute.RH_of_shifted_atom_route
├→ Q3.Weil_criterion
└→ Q3.Proofs.PaperMainlineAtomRoute.Q_nonneg_on_Weil_cone_current_atom_route
   → Q3.Proofs.CompatibilityReduction.Q_nonneg_on_WK_tcritical_current_atom_route
   → Q3.Proofs.CompatibilityReduction.Q_nonneg_on_WK_tcritical_of_shifted_evenized_atoms
   → Q3.T5.T5_transfer_of_atoms
   → Q3.Q_Fejer_heat_atom_nonneg_t_critical
   → Q3.Q_phi_shift_nonneg_t_critical
   → Q3.prime_term_le_at_t_critical
   → Q3.prime_term_le_at_t_critical_axiom
```

Corrected interface graph:

```text
Q3.RH_of_weil_geometric_sign_replacement
→ Q3.RH_of_global_weil_positivity
├→ explicit Q3.ExactWeilCriterion
└→ explicit Q3.GlobalWeilPositivity
```

## Theorem-level reverse dependencies

```yaml
Q3.Proofs.PaperMainlineAtomRoute.RH_of_shifted_atom_route:
  - Q3.RH_of_shifted_atom_route
Q3.RH_of_shifted_atom_route:
  - Q3.Main.RH_of_Weil_and_Q3
  - Q3.MainTheorems.RH_proven@Q3/MainTheorems.lean
Q3.Proofs.PaperMainlineAtomRoute.Q_nonneg_on_Weil_cone_current_atom_route:
  - Q3.Q_nonneg_on_Weil_cone_current_atom_route
  - Q3.Proofs.PaperMainlineAtomRoute.RH_of_shifted_atom_route
Q3.Q_nonneg_on_Weil_cone_current_atom_route:
  - Q3.Main.Q_nonneg_on_Weil_cone
Q3.Main.Q_nonneg_on_Weil_cone:
  - Q3.MainTheorems.Q_nonneg_Weil_cone@root_MainTheorems
Q3.RH_of_global_weil_positivity:
  - Q3.RH_of_weil_geometric_sign_replacement
Q3.RouteB.rh_iff_centeredXi_zeros_real:
  - Q3.RouteB.CanonicalRHRoute.rh_of_canonical_strip_slots
Q3.RouteB.CanonicalRHRoute.rh_of_canonical_strip_slots:
  - Q3.RouteB.CanonicalRHRoute.rh_of_canonical_slots
Q3.MainTheorems.Q_nonneg_Weil_cone@root_MainTheorems:
  - Q3.MainTheorems.RH_proven@root_MainTheorems
```

The duplicate root-file proof has its own forward branch:

```text
Q3.MainTheorems.RH_proven@root_MainTheorems
├→ Q3.Weil_criterion
└→ Q3.MainTheorems.Q_nonneg_Weil_cone@root_MainTheorems
   → Q3.Main.Q_nonneg_on_Weil_cone
```

Direct importers of `Q3.Main`:

```text
q3.lean.aristotle/Q3.lean
q3.lean.aristotle/Q3/CheckAxioms.lean
q3.lean.aristotle/Q3/MainTheorems.lean
q3.lean.aristotle/CheckAxioms.lean
q3.lean.aristotle/MainTheorems.lean
q3.lean.aristotle/check_axioms.lean
q3.lean.aristotle/scripts/full_consistency_check.lean
```

## Reproduction

Run from `q3.lean.aristotle` with the pinned Lean toolchain:

```bash
env -u LD_LIBRARY_PATH lake env lean Q3/CheckAxioms.lean
env -u LD_LIBRARY_PATH lake env lean Q3/MainTheorems.lean
env -u LD_LIBRARY_PATH lake env lean MainTheorems.lean
env -u LD_LIBRARY_PATH lake build Q3.Clean.MainClean
sha256sum Q3/MainTheorems.lean MainTheorems.lean
printf '%s\n' \
  'import Q3.Main' \
  '#print axioms Q3.Proofs.PaperMainlineAtomRoute.Q_nonneg_on_Weil_cone_current_atom_route' \
  '#print axioms Q3.Proofs.PaperMainlineAtomRoute.RH_of_shifted_atom_route' \
  '#print axioms Q3.Q_nonneg_on_Weil_cone_current_atom_route' \
  '#print axioms Q3.Main.Q_nonneg_on_Weil_cone' \
  | env -u LD_LIBRARY_PATH lake env lean --stdin
sed '$a #print axioms Q3.MainTheorems.Q_nonneg_Weil_cone' MainTheorems.lean \
  | env -u LD_LIBRARY_PATH lake env lean --stdin
printf '%s\n' \
  'import Q3.Basic.WeilDirectRoute' \
  '#print axioms Q3.RH_of_global_weil_positivity' \
  '#print axioms Q3.RH_of_weil_geometric_sign_replacement' \
  | env -u LD_LIBRARY_PATH lake env lean --stdin
printf '%s\n' \
  'import Q3.Proofs.RouteB.CanonicalRHRouteSkeleton' \
  '#print axioms Q3.RouteB.rh_iff_centeredXi_zeros_real' \
  '#print axioms Q3.RouteB.CanonicalRHRoute.rh_of_canonical_strip_slots' \
  '#print axioms Q3.RouteB.CanonicalRHRoute.rh_of_canonical_slots' \
  | env -u LD_LIBRARY_PATH lake env lean --stdin
```

## Honest status

```yaml
unconditional_rh_proof: false
compiled_broad_cone_export: CONDITIONAL_COMPILED
corrected_square_class_interfaces: OPEN_CONDITIONAL_INTERFACES
clean_surface: LEGACY_BUILD_FAILED
route_b: CHALLENGER_NOT_RH
canonical_public_entrypoint_established: false
```
