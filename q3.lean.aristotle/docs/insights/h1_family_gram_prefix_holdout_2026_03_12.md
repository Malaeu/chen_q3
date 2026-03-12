# H1 `family-gram-prefix` holdout verdict for `(++ )` (2026-03-12)

## Context

The pooled `family-gram-a` experiment gave the first strong in-sample sign that
one common `(++ )` basis might exist for fixed `a`, `zeros`, and defect rank.
But that basis was still built using the full tested `M`-grid itself.

So the next honest question was stricter:

```text
does a prefix-only pooled basis from smaller M values already explain
the next M-level well?
```

This is implemented as `--basis-choice family-gram-prefix`.

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
  --sweep-M-values 4,5,6,7 \
  --sweep-zero-values 40 \
  --rank-sweep-values 4,5 \
  --basis-choice family-gram-prefix
```

## Main result

The honest prefix holdout fails badly.

For rank `4`, the direct projected residuals are:

- `a=1.0`: `M=5 ~ 5.46e-1`, `M=6 ~ 4.72e-1`, `M=7 ~ 4.39e-1`;
- `a=1.25`: `M=5 ~ 5.40e-1`, `M=6 ~ 4.80e-1`, `M=7 ~ 4.35e-1`.

For rank `5`, the direct projected residuals are still large:

- `a=1.0`: `M=5 ~ 5.46e-1`, `M=6 ~ 4.72e-1`, `M=7 ~ 4.39e-1`;
- `a=1.25`: `M=5 ~ 5.40e-1`, `M=6 ~ 4.80e-1`, `M=7 ~ 4.35e-1`.

The embedding transfer is no better:

- rank `4`: `~6.10e-1 .. 6.75e-1`;
- rank `5`: `~6.10e-1 .. 6.75e-1`.

Summary:

- `family-gram-prefix`: `min ~ 4.35e-1`, `max ~ 5.46e-1`, `avg ~ 4.86e-1`.

## Interpretation

This does **not** kill Branch A.

But it kills the stronger upgrade that the pooled `family-gram-a` signal might
have suggested:

```text
there is not yet any honest theorem-grade prefix-stable common (++ ) basis
visible on the tested grid.
```

So the honest status is now:

- pooled `family-gram-a`: strong in-sample common-basis signal;
- `family-gram-prefix`: negative holdout;
- Branch A: still alive only in split case `B`;
- no upgrade yet to a common-basis theorem shape across `M`.

## Consequence for the route

The next task is **not** augmented cap positivity yet.

The next task is narrower:

```text
(++ ) alternative weighted Gram / higher-rank / basis redesign
under the same frozen kappa_{+-}(a).
```

If that fails too, the theorem will likely have to remain explicitly
family-dependent and `M`-dependent at the defect-space level.
