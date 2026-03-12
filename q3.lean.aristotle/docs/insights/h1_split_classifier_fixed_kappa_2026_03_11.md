# H1 split classifier with fixed `\kappa_{+-}(a)` (2026-03-11)

## Setup

We upgraded `src/h1_filtered_bulk_match.py` with a dedicated split-classifier
mode:

- fit one common `\kappa(a)` from a chosen source family or freeze it;
- apply that same scale to both live families `(++),(+-)`;
- compare three basis choices for the hard family:
  `low-mode`, `joint-gram`, `family-specific`,
  together with explicit `M -> M+1` embedding/transfer checks.

Canonical command used for the first real split run:

```bash
cd /Users/emalam/Documents/GitHub/rh_lean_01_2026
source .venv/bin/activate
python -u src/h1_filtered_bulk_match.py \
  --split-classifier \
  --classifier-family ++ \
  --fit-kappa-from-family +- \
  --fit-kappa-scope a-grid \
  --sweep-a-values 1.0,1.25 \
  --sweep-M-values 4,5,6 \
  --sweep-zero-values 40 \
  --rank-sweep-values 3,4,5,6 \
  --basis-choice all
```

This freezes `zeros=40`, fits one pooled `\kappa_{+-}(a)` for each fixed `a`,
and then tests only the hard `++` family under that common scale.

## Common `\kappa(a)` extracted from `(+,-)`

The pooled `(+,-)` fit is stable across `M=4,5,6`:

- `a=1.0`:
  `\kappa_{+-}(1.0) ~= 4.362257071335e-03 + 8.437337406607e-04 i`
- `a=1.25`:
  `\kappa_{+-}(1.25) ~= -5.243808071585e-04 - 1.938275280770e-02 i`

So the shared structural object that survives cleanly is indeed the scale
`\kappa(a)`, not a joint defect basis.

## `(+,-)` remains the easy calibration family

Under the same pooled `\kappa_{+-}(a)`, the `(+,-)` residual still looks
structured and easy:

- `a=1.0`, `rank=3`: `proj rel` stays around
  `6.48e-4`, `6.46e-4`, `9.52e-4` for `M=4,5,6`;
- `a=1.25`, `rank=3`: `6.28e-3`, `1.21e-3`, `3.28e-3` for `M=4,5,6`.

This is fully compatible with the working picture:

```text
(+-) = stable calibration family.
```

## `(++ )` is the only hard family

### Low-mode basis

The standard low-mode basis is decisively bad in every nontrivial case.

At `rank=3`:

- `a=1.0`: `6.25e-1`, `7.61e-1`, `8.15e-1` for `M=4,5,6`;
- `a=1.25`: `6.19e-1`, `7.50e-1`, `8.15e-1`.

At `rank=4`:

- `a=1.0`: `M=5 -> 5.57e-1`, `M=6 -> 6.71e-1`;
- `a=1.25`: `M=5 -> 5.41e-1`, `M=6 -> 6.75e-1`.

At `rank=5`, still nontrivial on `M=6`:

- `a=1.0 -> 4.51e-1`;
- `a=1.25 -> 4.80e-1`.

So the old “low-mode defect” story is dead even after freezing
`\kappa_{+-}(a)`.

### Family-specific basis

For `(++ )`, the family-specific rank-`r` basis is clearly the strongest model.

At `rank=3`:

- `a=1.0`: `2.54e-2`, `4.01e-2`, `5.23e-2` for `M=4,5,6`;
- `a=1.25`: `1.55e-3`, `7.96e-3`, `1.37e-2`.

At `rank=4`:

- `a=1.0`: `M=5 -> 5.35e-3`, `M=6 -> 1.34e-2`;
- `a=1.25`: `M=5 -> 1.12e-4`, `M=6 -> 7.18e-3`.

At `rank=5`:

- `a=1.0`, `M=6 -> 2.77e-3`;
- `a=1.25`, `M=6 -> 1.90e-3`.

Important caveat:

- `rank=4` on `M=4`,
- `rank=5` on `M=5`,
- `rank=6` on `M=6`

are tautological exact fits because the matrix size is already exhausted.
The nontrivial evidence is therefore:

- `rank=3` on `M=4,5,6`;
- `rank=4` on `M=5,6`;
- `rank=5` on `M=6`.

This points to a plausible split-form defect of effective rank about `4` through
`M=5`, and about `5` through `M=6`.

### Joint-Gram basis

The same-run joint-Gram basis is weaker than the family-specific one, but still
far better than low-mode:

- `a=1.0`, `rank=4`, `M=5 -> 5.65e-2`, `M=6 -> 7.28e-2`;
- `a=1.25`, `rank=4`, `M=5 -> 1.11e-2`, `M=6 -> 1.60e-2`;
- `a=1.0`, `rank=5`, `M=6 -> 2.89e-2`;
- `a=1.25`, `rank=5`, `M=6 -> 8.81e-3`.

So a joint same-run basis is not absurd, but it is consistently worse than the
family-specific `++` basis and is not yet theorem-grade.

### `M -> M+1` embedding stability

This is where the theorem-grade obstruction still sits.

For `(++ )`, the embedded transfer residuals remain large:

- `rank=3`:
  family-specific and joint-Gram both stay around `4.5e-1 .. 5.6e-1`;
- `rank=4`:
  again about `4.5e-1 .. 5.6e-1`;
- `rank=5`:
  about `4.5e-1 .. 4.8e-1` on the only nontrivial `M=5 -> 6` step.

The corresponding principal angles are moderate-to-large, not theorem-clean:

- family-specific:
  third/fourth/fifth angles typically land between `~40°` and `~80°`;
- joint-Gram:
  same scale, often still with a large last angle between `~38°` and `~87°`;
- low-mode:
  trivial subspace alignment under embedding, but the transfer residual stays
  bad because the basis itself is wrong.

So the current honest classifier verdict is:

```text
Case A (stable shared small-rank defect-space): not seen.
Case B (family-dependent finite-rank defect): plausible and currently live.
Case C (genuine bulk mismatch): not supported by the current numbers.
```

## Working theorem consequence

The data now strongly support the split theorem shape:

```text
one common scale kappa(a),
but separate defect structures for (++ ) and (+,-).
```

The correct live next question is no longer
“is there one joint rank-3 cap-space?” but:

```text
does (++ ) admit a stable higher-rank or better-adapted basis,
or must the split theorem allow genuinely family-dependent defect spaces?
```

## Practical next step

Do **not** move to augmented cap positivity yet.

Next executable task:

1. keep `zeros=40` frozen;
2. keep `\kappa(a)=\kappa_{+-}(a)` frozen by pooled `(+,-)` fit;
3. continue only on `(++ )`;
4. test alternative `++` basis choices / Gram projections beyond the current
   joint and naive embedded models;
5. treat `rank=4` and `rank=5` as the real live window;
6. keep Branch A provisionally blessed in split form unless this higher-rank
   `(++ )` story collapses at the next `M`.
