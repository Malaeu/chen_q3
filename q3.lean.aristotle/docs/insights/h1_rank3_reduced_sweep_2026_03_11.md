# H1 rank-3 reduced sweep verdict (2026-03-11)

## Status

Reduced Gate A sweep completed after the full `4 x 4 x 3` grid proved too slow
to be decision-efficient on the current machine.

The reduced grid was chosen to test exactly the live theorem-shape:

- core band:
  `a in {1.0, 1.25}`,
  `M in {4, 5}`,
  `zeros in {20, 40}`;
- edge sanity:
  `a in {0.8, 1.5}`,
  `M = 4`,
  `zeros in {20, 40}`;
- always with `defect-rank = 3`.

## What stayed true

- pure low-mode support still looks false;
- a small-rank structured correction still looks plausible on each family
  separately;
- zero-count stability is excellent: moving `zeros 20 -> 40` barely changes the
  per-run verdicts or the shared-basis geometry.

## What failed

The global working hypothesis

`shared rank-3 joint cap defect after the right joint basis / Gram projection`

does **not** survive the reduced sweep as a uniform theorem-shape.

## Key observations

### Edge regime

- `a=0.8, M=4` is bad at both `zeros=20,40`:
  `proj_rel_resid(++) ~ 8.24e-1`,
  `proj_rel_resid(+-) ~ 2.04e-3`,
  with third principal angle near `58°`;
- `a=1.5, M=4` is good at both `zeros=20,40`:
  `proj_rel_resid(++) ~ 3.6e-3`,
  `proj_rel_resid(+-) ~ 1.1e-3`.

So the rank-3 shared space is not even approximately uniform in `a`.

### Core band, `M=4`

- `a=1.0, M=4` remains good:
  `proj_rel_resid(++) ~ 1.94e-2`,
  `proj_rel_resid(+-) ~ 1.68e-3`;
- `a=1.25, M=4` remains good:
  `proj_rel_resid(++) ~ 7.9e-3`,
  `proj_rel_resid(+-) ~ 1.1e-3`.

So the candidate was not a hallucination: there is a real local structured
window.

### Core band, `M=5`

- `a=1.0, M=5` breaks sharply:
  `proj_rel_resid(++) ~ 8.32e-1`,
  `proj_rel_resid(+-) ~ 2.42e-3`;
- `a=1.25, M=5` degrades less brutally but still fails as a small shared cap:
  `proj_rel_resid(++) ~ 1.51e-1`,
  `proj_rel_resid(+-) ~ 3.31e-3`.

The shared-basis `M_step` angles also become large:

- `a=1.0`, `M:4 -> 5`: third angle about `79.3°`;
- `a=1.25`, `M:4 -> 5`: third angle about `79.7°`.

Embedded-basis transfer is therefore bad exactly where a theorem-grade
finite-dimensional shared cap would need to stay stable.

## Honest verdict

- `shared rank-3 joint cap defect` is now `false-for-now` as a **global**
  theorem-shape;
- the strongest surviving statement is still
  `structured finite-rank correction yes`,
  but likely **family-dependent** or requiring a different / larger common
  space;
- the cleanest immediate split is now:
  `(++ ) classifier` versus `(+-) classifier`.

## Recommended next step

Do **not** move to augmented cap positivity yet.

Instead:

1. treat `+-` as the stable easy family;
2. isolate `++` as the hard family;
3. test whether `++` needs:
   a higher shared rank,
   a different joint basis,
   or a genuinely family-dependent correction;
4. only after that revisit augmented cap absorption.
