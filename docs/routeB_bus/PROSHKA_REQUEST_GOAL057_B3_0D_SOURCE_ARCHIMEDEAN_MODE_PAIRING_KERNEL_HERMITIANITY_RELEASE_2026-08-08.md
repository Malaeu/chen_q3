# PROSHKA REQUEST — Goal 057 B3.0D source archimedean mode-pairing kernel Hermitianity release

## 0. Requested decision

Return exactly one primary operational verdict for the smallest next atom
after the proved B3.0C transaction:

`GOAL057_B3_0D_SOURCE_ARCHIMEDEAN_MODE_PAIRING_KERNEL_HERMITIANITY`

Candidate A is:

`TRY_GOAL057_B3_0D_SOURCE_ARCHIMEDEAN_MODE_PAIRING_KERNEL_HERMITIANITY`

If Candidate A is source-faithful and minimal, release it with the exact Lean
contract and mandatory plants.  Otherwise return one `KILL_` or `WALL_`
code naming the first missing source fact and the smallest repaired atom.

This is one `DELEGATED_STRATEGIC_REVIEW` in the same living Goal 057 phase
and same living conversation.  It is not an owner boundary.

## 1. Immutable control state

```yaml
repo: /Users/emalam/GitHub/rh_lean_01_2026
branch: rh_clean
head: a97fc22ba8b0179deeabbd1321f83c9737084925
origin_rh_clean: a97fc22ba8b0179deeabbd1321f83c9737084925
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
parent_request_message_id: 906a704a-7268-494c-ba26-a2b3f117b71f
parent_response_message_id: 00ac7aad-f7e2-43cd-b0e9-4134ff20eefc
```

Do not create Bus 010, decrement the ten-checkpoint ledger, invoke H4a1b,
promote Route B, or claim RH.

## 2. Closed parent B3.0C

Production file:

`Q3/Proofs/RouteB/D0PstarSourceArchModePairingIntegrable.lean`

SHA-256:

`cdad33d4e428dc541501d24b3254e72b3f01b3aae36bb482d5d59476bb16f27a`

Exact theorem:

```lean
theorem sourceArchimedeanModePairing_integrable
    (i : PairIndex) (n r : ℤ) :
    Integrable
      (fun t : ℝ =>
        conj (𝓕 (logWindowZeroExtendedMode i n) t) *
          (sourceArchimedeanMultiplier t : ℂ) *
          𝓕 (logWindowZeroExtendedMode i r) t)
```

Validation is complete: direct Lean, target build 7,763, full build 7,817,
`q3_check`, 80/80 unit tests, strict Spine, 9/9 plants, 4/4 proof-DB
declarations, three SQLite integrity checks, and standard axioms only.

B3.0C is closed.  B3.0 remains open.  The coarse ledger remains 0/10.

Closeout SHA-256:

`44f6ae88dad05116c63e47a8b73000351abc3081394e973dd8989b3b46b299e8`

Goal A15 SHA-256:

`3d458caecf836234f19245b318e7c4d8b80da820e4cedaa4beb2bbdcf382e68f`

## 3. Source orientation and reality lock

Source-lock file:

`ACTIVE/requests/routeB_lamport_rh_closure/D0_2_EXACT_WEIL_SESQUILINEAR_FORM.md`

SHA-256:

`52c58cee35344edc5baa30f3e2028b402c9a64a0e9a08c4dd093557a5a561308`

It fixes

```text
QW(f,g) = Psi(f^* * g)
BW_m_N(f,g) = sum_(r,s) conjugate(c_r) tau_(r,s) d_s
```

so the first mode is conjugated and the second is linear.  Separately, the
production definition has exact type

```lean
sourceArchimedeanMultiplier : ℝ → ℝ
```

therefore its coercion to `ℂ` is fixed by conjugation pointwise.  No
nonvanishing or sign premise is required for the symmetry identity.

## 4. Intended public surface from the parent verdict

The B3.0C verdict named this exact intended surface without authorizing it:

```lean
noncomputable def sourceArchimedeanModePairing
    (i : PairIndex) (n r : ℤ) : ℂ :=
  ∫ t : ℝ,
    conj (𝓕 (logWindowZeroExtendedMode i n) t) *
      (sourceArchimedeanMultiplier t : ℂ) *
      𝓕 (logWindowZeroExtendedMode i r) t

theorem sourceArchimedeanModePairing_conj_symm
    (i : PairIndex) (n r : ℤ) :
    sourceArchimedeanModePairing i r n =
      conj (sourceArchimedeanModePairing i n r)
```

Proposed owned file:

`Q3/Proofs/RouteB/D0PstarSourceArchModePairingKernel.lean`

Proposed exact import:

```lean
import Q3.Proofs.RouteB.D0PstarSourceArchModePairingIntegrable
```

Proposed public surface: exactly one noncomputable definition and one theorem;
zero public structures and zero extra axioms.

If the owned filename or theorem orientation should differ, pin the corrected
contract in the verdict rather than silently widening the atom.

## 5. Source-compiled preflight

Scratch outside the repository:

`/tmp/Goal057B3_0D_Scratch.lean`

- SHA-256:
  `fd319acf46f63c805d9e71706b8429be144d640c82a3cc4308d4f9dfc15c1b2c`.
- Size: 856 bytes / 26 lines.
- Command:
  `lake env lean /tmp/Goal057B3_0D_Scratch.lean`.
- Result: **PASS** under the production toolchain.

The proof is source-exact and uses no analytic strengthening:

1. unfold the pairing definition;
2. rewrite the conjugated integral by Mathlib's `integral_conj`;
3. simplify conjugation of multiplication, double conjugation, and the real
   multiplier coercion;
4. close the commutative scalar identity by `ring`.

Official Mathlib API:

https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.html#integral_conj

The theorem needs no integrability hypothesis syntactically because
`integral_conj` is total, but B3.0C remains the semantic certificate that
the kernel integral is the intended legal `L¹` pairing.

## 6. Why this is the smallest honest next atom

- It materializes exactly the next public surface named by the parent verdict.
- It preserves the source antilinear-first index orientation.
- It consumes the B3.0C `L¹` carrier without introducing a new premise.
- It proves only conjugate symmetry of the archimedean mode kernel.
- It does not manufacture the prime or pole contributions.
- It does not identify the kernel with the full source Weil form.
- It does not construct an associated operator graph or domain.
- It does not promote fixed modes to uniform/cofinal control.

The parent wall after success remains:

`SOURCE_WEIL_FORM_FOURIER_MULTIPLIER_DECOMPOSITION`

## 7. Proposed private support budget

Zero private theorems are needed by the compiled preflight.  Permit at most one
private pointwise-conjugation helper only if the exact production API requires
it.  Do not add an abstract structure or premise-only wrapper.

## 8. Mandatory plants

Return exact mutations and stop codes, at minimum covering:

1. `P057_B3_0D_1_MODE_INDEX_ORIENTATION`
   - swap `n,r` without the matching conjugation;
   - required code: `SOURCE_MODE_PAIRING_INDEX_ORIENTATION_MISMATCH`.
2. `P057_B3_0D_2_ANTILINEAR_FIRST`
   - delete first-slot conjugation or conjugate the second slot;
   - required code: `SOURCE_FORM_ANTILINEAR_FIRST_ORIENTATION_MISMATCH`.
3. `P057_B3_0D_3_MULTIPLIER_REALITY`
   - replace the real source multiplier by an unconstrained complex symbol;
   - required code: `SOURCE_ARCH_MULTIPLIER_REALITY_MISSING`.
4. `P057_B3_0D_4_INTEGRAL_VALUE_HALLUCINATION`
   - assert a diagonal sign, positivity, or closed-form value;
   - required code: `SOURCE_ARCH_PAIRING_VALUE_NOT_PROVED`.
5. `P057_B3_0D_5_KERNEL_AS_FULL_SOURCE_FORM`
   - identify the archimedean kernel with the full source Weil form;
   - required code: `SOURCE_WEIL_FORM_DECOMPOSITION_MISSING`.
6. `P057_B3_0D_6_FORM_TO_OPERATOR_GRAPH`
   - treat kernel Hermitianity as an associated-operator graph/domain theorem;
   - required code: `FORM_DOMAIN_NOT_OPERATOR_DOMAIN`.
7. `P057_B3_0D_7_FIXED_TO_UNIFORM`
   - promote fixed `(n,r)` symmetry to uniform/cofinal control;
   - required code: `UNIFORM_COFINAL_MODE_BOUND_MISSING`.
8. `P057_B3_0D_8_GENERATED_BACKEND_IMPORT`
   - inject generated PSD/Step33/hbox/payload support;
   - required code: `ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK`.
9. `P057_B3_0D_9_DIAGONAL_REALITY`
   - remove first-slot conjugation in the diagonal control;
   - required code: `SOURCE_ARCH_PAIRING_DIAGONAL_REALITY_MISMATCH`.

All mutation artifacts must remain outside production and be removed after
testing.

## 9. Required response schema

```yaml
STATUS: OPEN
PRIMARY: TRY_|KILL_|WALL_
RELEASED_ATOM:
OWNED_FILE:
EXACT_IMPORTS:
EXACT_PUBLIC_DEFINITIONS:
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

1. source-faithfulness check for conjugation and `n,r` orientation;
2. minimal Lean proof plan using the pinned API;
3. strongest attack against route progress;
4. exact semantic boundary after success;
5. smallest next atom, without authorizing it unless separately stated.

## 10. Boundary

This request authorizes no production Lean edit by itself.  Codex may create
the owned file only after an operative `TRY_` release.  The sole owner gate
remains `PX_RH_CLAIM`; promotion and every RH statement remain forbidden.
