# H1 pooled `family-gram-a` basis for `(++ )` (2026-03-12)

## Context

After the fixed-`kappa_{+-}(a)` split classifier, the remaining live question
for Branch A was:

```text
can one find a better `(++ )` family-specific basis / Gram projection
that stabilizes across M?
```

The old picture was:

- low-mode dead;
- joint-Gram intermediate;
- family-specific best inside each fixed `M`;
- but `M -> M+1` transfer for both joint-Gram and family-specific bases still
  sat around `4.5e-1 .. 5.6e-1`.

So the next honest try was an explicitly pooled `(++ )` basis:

```text
family-gram-a = one common basis for fixed (a, zeros, rank),
built from the ++ residual matrices across the tested M-grid.
```

This is now implemented in `src/h1_filtered_bulk_match.py` as
`--basis-choice family-gram-a`.

## Command

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
  --rank-sweep-values 4,5 \
  --basis-choice all
```

## Main result

The pooled `family-gram-a` basis is the first candidate that really improves
the `(++ )` transfer story.

### Rank `4`

For `a=1.0`:

- `M=5`: `proj_rel_resid ~= 4.91e-2`;
- `M=6`: `proj_rel_resid ~= 7.53e-2`.

For `a=1.25`:

- `M=5`: `proj_rel_resid ~= 1.24e-2`;
- `M=6`: `proj_rel_resid ~= 1.91e-2`.

### Rank `5`

The only nontrivial step is `M=6`:

- `a=1.0`: `proj_rel_resid ~= 3.00e-2`;
- `a=1.25`: `proj_rel_resid ~= 1.08e-2`.

## Comparison against previous bases

Summary on the same run:

- low-mode:
  `max ~= 6.75e-1`, `avg ~= 2.81e-1`;
- joint-Gram:
  `max ~= 7.28e-2`, `avg ~= 1.62e-2`;
- family-gram-a:
  `max ~= 7.53e-2`, `avg ~= 1.64e-2`;
- family-specific:
  `max ~= 1.34e-2`, `avg ~= 2.56e-3`.

So inside each fixed `M`, `family-specific` still wins.
But for the transfer problem, `family-gram-a` is dramatically better than the
older transfer tests:

- old joint-Gram / family-specific `M -> M+1` transfer:
  about `4.5e-1 .. 5.6e-1`;
- new pooled `family-gram-a` transfer:
  about `1.24e-2 .. 7.53e-2` on the live nontrivial rank window.

That is the first honest numerical sign that one common `(++ )` family basis
may exist for fixed `a`.

## Interpretation

This does **not** prove theorem-grade stability yet, because the basis is
pooled across the tested `M` values and is therefore still an in-sample common
basis.

But it does change the Branch A verdict materially:

```text
At the in-sample level, Branch A is strongly blessed in split case B.
```

More precisely:

- low-mode defect: dead;
- shared joint rank-3 story: dead globally;
- family-dependent finite-rank `(++ )` defect: strongly alive;
- one pooled family-specific common basis across tested `M`:
  now numerically plausible.

## Immediate next kill-test

The next honest stress test is no longer “is there any basis at all?”, because
the answer is now plausibly yes.

The next honest stress test is:

```text
prefix / leave-one-out family-gram basis,
or extension to M=7,
under the same frozen kappa_{+-}(a).
```

If the pooled `family-gram-a` story survives one of those stricter tests, then
Branch A stops looking merely plausible and starts looking genuinely theorem-
shaped in split form.

## Update

The stricter same-day holdout `family-gram-prefix` did **not** confirm a
theorem-grade common basis yet:

- direct projected residuals on `M=5,6,7` stayed around `~4.35e-1 .. 5.46e-1`;
- `M -> M+1` transfer stayed around `~6.10e-1 .. 6.75e-1`.

So this note should now be read as an in-sample signal only.
For the honest follow-up verdict, see
`docs/insights/h1_family_gram_prefix_holdout_2026_03_12.md`.
