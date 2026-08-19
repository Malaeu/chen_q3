# STATUS: GREEN — CANONICAL SCHUR BRIDGE VALIDATED; APPLIED FROM MBOX BECAUSE THE JUDGE HAD NO WRITE ACTIONS

```yaml
PRIMARY: COFINAL_FIXED_SHIFT_LITERAL_COMPLEMENT_FLOOR_SCHUR_BRIDGE_LEAN

REPO: Malaeu/chen_q3
BRANCH: rh_clean
GATE_RUN_BY: LINUX_BODY

DELIVERY: MBOX_APPLIED_BY_LINUX_BODY
DELIVERY_REASON: judge runtime exposed no create_blob/create_tree/create_commit/update_ref
MBOX_SHA256: 5585001959cbc3755a57ac32653e7357f0b2cb90880cb7f3f0d8c112b5260a33
MBOX_SHA256_VERIFIED: true
PATCH_1_APPLIED: fbc74a5b
PATCH_2_SKIPPED: creates the green verdict already landed in 49767fac, same blob 6254c24b
PREFIX_RESTORED_BY_AMEND: git am strips leading [..] from the subject
AUTHOR_PRESERVED: Proshka <146065732+Malaeu@users.noreply.github.com>

RECEIPTS_AFTER_APPLY:
  lean_blob: ee595474ab798b81ae2ce7c9d7f4262cc17763e8   # matches
  lean_sha256: 24608fbeb121de39369747217dd6beb66dadfe4dcdc684fecce06bdb3172bc83  # matches
  source_record_blob: 7a936fab3ebe56bfbcf19a0555a5acb8b95f7623   # matches

FIRST_GATE: RED
FIRST_GATE_EXIT: 1
FIRST_GATE_ERRORS:
  - "205:23 Invalid field smul: no Eq.smul"
  - "250:23 Unknown constant Matrix.PosSemidef.fromBlocks₂₂"
  - "301:2 type mismatch: PosDef 1 vs !![1].PosDef"

LINUX_REPAIR: technique only, 12 insertions 4 deletions
FINAL_LEAN_SHA256: a65207ec8647f692772311df08407355d2331b2b4f5a716ad8dde86cd917866d
SHAPE: 13273_BYTES_334_NEWLINE_TERMINATED_LINES_FINAL_LF
FINAL_GATE: GREEN
FINAL_EXIT: 0
Q3_CHECK: ok
AXIOMS_ALL_SIX: [propext, Classical.choice, Quot.sound]

SCOPE: COFINAL_FAMILY
VERIFIER: LEAN

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## 1. The new defect class

For the first time the break was an external lemma name, not a local tactic.

The source record declared `theorem_engine: Matrix.PosSemidef.fromBlocks₂₂`. No
such constant exists. The lemma is real and sits at
`Mathlib/LinearAlgebra/Matrix/PosDef.lean:549`, inside `namespace PosDef`, so its
full name is `Matrix.PosDef.fromBlocks₂₂`. Its signature is exactly what the
source assumed — `(A) (B) {D} (hD : D.PosDef) [Invertible D]` returning an `iff`
whose `.2` direction was used correctly. The mathematics was right; the address
was wrong.

Two further breaks: `Matrix.IsHermitian.smul` does not exist in Mathlib at all,
so the scalar-multiple case is now proved directly through `conjTranspose_smul`;
and `!![1]` does not reduce to the identity matrix, so the tail plant routes
through an explicit equality before `Matrix.PosDef.one`.

This class is worth naming because the usual reflex does not catch it: a name
that reads plausibly and belongs to a lemma that genuinely exists, one namespace
away. `rg` over the Mathlib source settles it in under a minute; nothing in the
project's own shelf can.

## 2. Delivery

The judge could not reach the ref: his runtime exposed read actions only. He said
so rather than claiming the source had landed, and shipped an mbox instead. It
applied cleanly, its sha256 matched, and all three post-apply receipts matched
the declaration.

One cost of the fallback path: `git am` strips leading bracketed tokens from the
subject, so `[Proshka][Goal058]` was removed and the commit stopped matching the
prefix grep that identifies his authorship. Restored by amend, with the author
field preserved. Direct writes do not have this failure mode.

## 3. What the node establishes

For one literal production cell the exact matrix

    M = Q (K - a* I) Q - beta Q,      Q = I - |q><q|

is reindexed by a precommitted head/tail split, and its head, coupling and tail
are the canonical `toBlocks` projections of that same matrix — not caller-supplied
certificates. A positive-definite tail plus a positive-semidefinite Schur
complement `A - B D⁻¹ Bᴴ` then certify `M ≥ 0`, hence the fixed-shift complement
floor, applied over the existing `selectedPairIndex = parent (extract k)`
schedule.

The plant `A = [-1]`, `B = [0]`, `D = [1]` is kernel-clean: the tail is strictly
positive while the full block is not positive semidefinite. Stopping after tail
coercivity is therefore refuted, not merely discouraged.

## 4. What it does not establish

Neither spectral sign is produced. The judge's own record says so:
`TAIL_POSDEF_PROVED_FOR_PRODUCTION_FAMILY_HERE: false` and
`CORRECTED_HEAD_PSD_PROVED_FOR_PRODUCTION_FAMILY_HERE: false`.

The open supplier list grows from four to six:

    CANONICAL_FIXED_SHIFT_TAIL_POSDEF_FAMILY          new
    CANONICAL_FIXED_SHIFT_CORRECTED_HEAD_PSD_FAMILY   new
    SOURCE_RAYLEIGH_PROXIMITY_TO_FIXED_SHIFT
    COMPACT_KERNEL_RATE_BUDGET
    LITERAL_SELECTED_FAMILY_MUNTZ_TAIL_DECAY
    THEOREM_510_REAL_ZERO_CROSSWALK

The wall did not fall; it split in two. His own strongest attack stands: the
corrected head may be no easier than the original floor.

## 5. Fate of registered predictions

    P_CFF_1  "source compiles unchanged", p=0.52   REFUTED
    P_CFF_2  "every printed profile within the standard triple", p=0.96  CONFIRMED
    P_CFF_3  "no public hypothesis reported unused", p=0.82  CONFIRMED
             — the three warnings are stylistic only.

The named failure class `SCHUR_BLOCK_NORMAL_FORM_OR_INVERTIBLE_INSTANCE` MISSED.
Canonical `toBlocks` normal form and the local `Invertible` instance both went
through without a single edit. The break was elsewhere entirely. First missed
class after two consecutive hits.

## 6. Next

    CANONICAL_FIXED_SHIFT_CORRECTED_HEAD_AND_TAIL_CERTIFICATE_FAMILY
