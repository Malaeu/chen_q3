# EStarMuntzContinuation v1 — FATAL archive record

- Status: `FATAL / DO_NOT_EXECUTE`
- Stop code: `ZETA_RAW_POLE_VALUE_MISMATCH`
- Contract SHA-256:
  `99fba49692fb9eec900e45a5f864572b77d7ea974739d1b7beed0f12c57f81d6`
- Archived contract:
  `ARISTOTLE_TASK_EStarMuntzContinuation_v1.md`
- Source artifact:
  `/Users/emalam/Downloads/ARISTOTLE_TASK_EStarMuntzContinuation.md`
- Adjudication:
  `../../proshka/PROSHKA_ZIP_AUDIT_FOLLOWUP_2026-07-27.md`
- Replacement contract:
  `../../ARISTOTLE_TASK_EStarMuntzContinuation_v2_REPAIRED.md`
- Archived: `2026-07-27`

## Fatal defect

`T4` and `T5` are false at the pole when they use the raw pointwise Mathlib
value

\[
\operatorname{riemannZeta}(w)\,\mathcal M h(w)
\]

at `w = 1`.  Zero mass makes the punctured singularity removable, but does
not make the raw point value equal to the removable value.  The raw value is
`0`, while the removable value is `deriv (Mellin h) 1`, which can be nonzero.
The repaired v2 contract uses `ZetaMellinReg` and keeps the raw-product
corollary only off the pole.

## H2 name split

- `MUNTZ_MASS_ZERO`: `∫₀∞ hλ(v) dv = 0` — `PASS`.
- `POISSON_ORIGIN_ZERO`: `hλ(0) = 0` — `FAIL`.

The first statement cancels the Müntz pole.  It does not remove the distinct
Poisson-origin counterterm governed by the second statement.
