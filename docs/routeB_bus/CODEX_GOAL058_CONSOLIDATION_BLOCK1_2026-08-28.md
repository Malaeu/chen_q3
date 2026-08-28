# Goal 058 consolidation — Block 1 closeout

```yaml
TASK_ID: GOAL058_CONSOLIDATION_BLOCK1
DATE: 2026-08-28
BODY: CODEX
STATUS: HOLD
SOURCE_TASK: docs/Codex/TASK_2026-08-28_goal058_consolidation.md
SOURCE_COMMIT: 56e144c49cae5f8c2dc80a09f6ca963a17dda88d
BASELINE_HEAD: d6ef83518a38a7e23db2c525c58532c67cbaf2d9
RH_CLAIM: false
PX_RH_CLAIM: NOT_MADE
CLOSES:
  - PROPOSITION59_CENTER_SAMPLING_AND_FULL_POLE_ROW
  - PROPOSITION59_FULL_INTEGER_ROW_NORM_CLOSED_FORM
  - ORIENTED_SMOOTH_MODEL_MASS_CEILING
  - POLARIZED_VOLTERRA_KERNEL_IDENTIFICATION
  - POLARIZED_HILBERT_WEIGHT_COMPLEX_MIXED_ZERO_MASS
  - GLOBAL_SECULAR_ZERO_POLE_COUNT_DIFFERENCE_ONE_UNDER_NORMALIZATION
OPENS:
  - ORIENTED_FULL_VOLTERRA_LITERAL_FUNCTIONAL_CATEGORY_AND_LEDGER_CROSSWALK
  - SECULAR_GAP_ROOT_MULTIPLICITY_PARITY_DEFINITION_AND_PROOF
```

## Result by mandatory cost order

| Item | Status | Kernel address | Exact boundary |
|---|---|---|---|
| (a) center | DONE | `proposition59PoleKernel_sum_at_zero`, `proposition59RawTransform_at_zero`, `proposition59RawTransform_at_zero_eq_sqrt` | The unnormalised sum is `L * v 0`; the raw transform is `sqrt L * v 0` for `L > 0`. |
| (b) pole row | DONE | `proposition59Pole_ne`, `proposition59PoleKernel_at_lattice`, `proposition59PoleKernel_at_lattice_sign`, `proposition59PoleKernel_sum_at_lattice` | The carrier guard `j ∈ S` is explicit. |
| (c) row norm | DONE | `proposition59PoleKernel_normSq_hasSum_at_lattice`, `proposition59PoleKernel_normSq_hasSum`, `proposition59PoleKernel_normSq_closedForm_tendsto_realAxis` | Exact equality is for the full unnormalised integer row. A finite carrier inherits only an upper bound. The off-real theorem assumes `L > 0` and `Im z ≠ 0`; the punctured real-axis limit is explicitly `L²`, while the lattice theorem separately gives the exact value `L²` at lattice points. |
| (d) smooth model mass | DONE | `goal058OrientedSmoothModelMass_le_six_div_pi`, `goal058OrientedSmoothModelMass_antitoneOn` | `6/pi` is an upper bound, not a finite-parameter equality. No identification with the literal prime source is claimed. |
| (e) polarized Volterra | DONE | `goal058PolarizedVolterraIntegral_eq_closed`, `goal058PolarizedHilbertWeight_sum_eq_zero` | Finite injective integer modes; exact complex mixed identity and zero mass. |
| (f) oriented functional | HOLD | none | The completed Arch channel is not a finite signed measure. Before the identity can enter Lean, the repository needs an endpoint-compensated test-functional category and a literal W02/Arch/Prime ledger crosswalk, including reflection by precomposition, signs, support, scalar-diagonal cancellation and endpoint integrability. The `2.5e-11` diagnostic is not proof authority. |
| (g) global count / local parity | SPLIT | `sourceLagrangePolynomial_natDegree_eq_card_sub_one` | The global degree difference is exact under the load-bearing normalization `(1 : n → ℝ) ⬝ᵥ xi = 1`. No local interval count follows. The local parity law remains HOLD until a multiplicity-aware gap-root count and its hypotheses are defined and proved. |

Block status is `HOLD`, not failure: five items and the global half of (g) are
kernel-green; (f) and the local half of (g) are deliberately not represented by
wrappers or numerical claims.

## Receipts and strongest attacks

- `ask.sh`, `knowledge.db`, the elaborated environment index and the live Lean
  tree were queried before implementation. No exact pre-existing suppliers were
  hidden by the prose reports.
- Independent preflight found the normalization trap in (a): applying the report's
  `L * v 0` literally to `proposition59RawTransform` would have been false.
- Independent audit of (f) found a category error, not a tactic gap: the
  archimedean object cannot be packaged as the finite signed measure printed in
  the report.
- Independent audit of (g) found that the cited local-count report was not the
  source of the global statement, and that the report's phrase "with no
  hypothesis" silently used the selected cell's normalization.
- The Volterra theorem consumes `Function.Injective mode`; without it the
  off-diagonal frequency denominator may vanish.

## Lifecycle side effects

### Assembly debt

No existing `assembly` row exactly names these representation assets. Therefore
no row was marked `READY` by name matching. The two HOLD objects above remain
mathematical debt; they are not disguised as new ready suppliers.

### Article debt

The new kernel addresses must enter the generated blueprint in Block 3. The two
HOLD objects must remain red. No prose is allowed to turn either into a theorem.

### Insight / failed-route debt

1. Never identify an unnormalised kernel sum with `proposition59RawTransform`.
2. Never model the completed Arch functional as a finite signed measure without
   endpoint compensation.
3. Never infer a local zero/pole count from a global degree difference.
4. A numerical equality is diagnostic only, even when it agrees to many digits.

## Validation contract

The block closes only after all changed Lean modules build, hole scans are empty,
the public declarations print exactly the standard axiom trio, derived indexes
are refreshed, the independent final review accepts the exact diff, and the
scoped block commit is pushed.
