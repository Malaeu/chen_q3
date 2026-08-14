# Goal 058 G3 — fixed-carrier backward-tail Schur convergence report

Date: `2026-08-14`

Status: `G3_MODE4_BACKWARD_TAIL_SCHUR_APPROX_TENDSTO_LITERAL_PROVED`

Boundary: one bounded local Codex leaf.  This report does not identify the new
matrix with an actual finite DLMF Schur complement, prove a Haynsworth
identity, prove an inertia count, prove offset zero, supply endpoint counts
`2/3`, close G1 or G3, promote Route B, or claim RH.

## Control and source lock

- base `HEAD = origin/rh_clean` before the leaf:
  `36bee52b`;
- worktree before the leaf: clean;
- repeated strict startup: `P9_STRICT_PASS`;
- Route state: `CHALLENGER_NOT_RH`;
- source packet:
  `GOAL058_G3_CLASSICAL_SPECTRUM_TO_LITERAL_SCHUR_INERTIA_SOURCE_PACKET_2026-08-14.md`;
- source-packet SHA-256:
  `2f8072b247e846641b7923974309bc76986108cf0779424c678ee878eae54f14`;
- accepted stability leaf:
  `D0Mode4HermitianNegativeCountStability.lean`;
- accepted stability-leaf SHA-256:
  `e410ff104210aac32b6e71f93e41f335ca9fe813944ce7ffd3b15dbd61429793`.

Knowledge preflight queries:

```text
Mode4BackwardTailSchurApproxTendstoLiteral
mode4BackwardTail mode4HermitianSchurMatrix fixed carrier Tendsto
```

Both returned `no hits`.  This is a discovery receipt, not a proof claim.

## Import-wall and bounded repair

The Proshka directive named the single direct import
`Q3.Proofs.RouteB.D0Mode4HermitianNegativeCountStability`.  Exact import-graph
inspection showed that this module imports
`D0Mode4SchurInertiaOrientation`, while the literal target
`mode4HermitianSchurMatrix` is defined only in the downstream sibling
`D0Mode4SchurHermitianSymmetrization`, which also imports the orientation
module.  The directed import therefore could not name its own target.

A repair query was sent to the standing Proshka chat.  The UI showed natural
reasoning time `6m 39s`, but the response ended as `Stopped thinking` without
a verdict.  No `Answer now` action was used.

The minimal executable repair was selected locally under the active
`CODEX_PROSHKA_FULL_EXCEPT_PX_RH_CLAIM` authority:

```lean
import Q3.Proofs.RouteB.D0Mode4SchurHermitianSymmetrization
```

It remains the only direct Q3 import.  The accepted stability leaf was not
edited and its accepted hash remains unchanged.  This convergence leaf does
not consume the stability theorem; later composition may import both leaves.

## Owned files

- `Q3/Proofs/RouteB/D0Mode4BackwardTailSchurConvergence.lean`;
- `ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_MODE4_BACKWARD_TAIL_SCHUR_CONVERGENCE_REPORT_2026-08-14.md`.

No Route, Bus, runtime, protocol, manifest, or other production path was
edited in this transaction.

## Exact public surface

Public definitions: exactly `1`.

```lean
noncomputable def mode4BackwardTailSchurApprox
    (mProject : ℕ) (Λ : ℝ) :
    (K d : ℕ) → Matrix (Fin K) (Fin K) ℝ
```

For `K = n+1`, this is the literal Hermitian Schur matrix formula with

```lean
mode4BackwardTail mProject Λ (n + 1) d 0
```

in place of

```lean
mode4RightTailLimit mProject Λ (n + 1)
```

in the newest `(0,0)` diagonal entry.  Every other entry is literally the
same fixed left-continuant/off-diagonal formula.

Public theorems: exactly `2`.

```lean
theorem mode4BackwardTailSchurApprox_isHermitian
    (mProject K d : ℕ) (Λ : ℝ) :
    (mode4BackwardTailSchurApprox mProject Λ K d).IsHermitian
```

```lean
theorem mode4BackwardTailSchurApprox_tendsto_literal
    (mProject K : ℕ)
    (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    Tendsto
      (fun d => mode4BackwardTailSchurApprox mProject Λ K d)
      atTop
      (𝓝 (mode4HermitianSchurMatrix mProject Λ K))
```

The convergence proof is entrywise.  Its only nonconstant branch is the
newest `(0,0)` entry, supplied directly by the existing scalar theorem
`mode4BackwardTail_tendsto_rightTailLimit` with terminal value zero.

## Strongest attack and boundary plant

`P-TAIL-4-ACTUAL-FINITE-SCHUR-RELABEL` is enforced as follows:

- the sole new definition is named `mode4BackwardTailSchurApprox`;
- the module and theorem docs state that it is not an actual finite Jacobi
  Schur complement;
- the declaration-name scan contains no `FiniteSchur` definition or theorem;
- no finite DLMF matrix, finite tail block, block inverse, Schur complement,
  congruence, or Haynsworth identity appears in the proof;
- the theorem concludes only `Tendsto` to the literal matrix.

Required mutation stop:
`G3_BACKWARD_TAIL_APPROX_RELABELLED_AS_ACTUAL_FINITE_SCHUR`.

Fixed-carrier guard: `K` is outside the approximating index `d`, so every
matrix has type `Matrix (Fin K) (Fin K) ℝ`.  No growing `Fin (d+1)` carrier is
admitted.

## Validation

All commands ran on the final Lean bytes.

```text
lake env lean Q3/Proofs/RouteB/D0Mode4BackwardTailSchurConvergence.lean
PASS

lake build Q3.Proofs.RouteB.D0Mode4BackwardTailSchurConvergence
PASS — 7751 jobs

lake build
PASS — 7817 jobs

bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4BackwardTailSchurConvergence.lean
PASS — q3_check ok

git diff --check
PASS
```

Public-surface scan:

```text
direct Q3 imports: 1
public definitions: 1
public theorems: 2
```

Forbidden-token scan found no `sorry`, `admit`, `exact?`, `native_decide`,
new `axiom`, or `opaque` declaration.

Both public theorems print exactly the standard axiom profile:

```text
[propext, Classical.choice, Quot.sound]
```

The only environmental warning is the pre-existing local-change warning in
the `.lake/packages/UnicodeBasic` dependency; no dependency file was touched.

## Result and remaining wall

```yaml
GENERIC_INERTIA_STABILITY: PROVED_PREVIOUS_LEAF
FIXED_CARRIER_BACKWARD_TAIL_SCHUR_APPROX: DEFINED
APPROX_HERMITIAN: PROVED
APPROX_TENDSTO_LITERAL_EXACT_TAIL_MATRIX: PROVED
ACTUAL_FINITE_DLMF_SCHUR_IDENTITY: NOT_PROVED
FINITE_TAIL_POSDEF: NOT_PROVED
HAYNSWORTH_INERTIA_EQUALITY: NOT_PROVED
DLMF_INDEXED_COUNT: NOT_FORMALIZED
OFFSET_ZERO: NOT_PROVED
ENDPOINT_COUNTS_2_3: NOT_AVAILABLE
G1: OPEN
G3: OPEN
ROUTE_B_PROMOTION: false
RH_CLAIM: false
```

The next source-locked gap is not more convergence.  It is the exact finite
DLMF matrix/crosswalk and the proof that its finite Schur complement is this
`Approx`; independently, the finite eliminated tail still needs a positive
definiteness theorem before Haynsworth can preserve negative count with zero
tail contribution.

No commit or push is authorized for this leaf in the current transaction.
