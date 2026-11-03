# Ground Fourier roots

`summary.csv` is the flat, current-input table. `raw_matches.csv` retains every one-to-one assignment and complex deviation; `raw_low_high_replay.csv` retains independently rebuilt-vector precision shifts. `aggregate.json` lists completed and missing integer cells, stale source receipts, and explicitly descriptive precision-qualified fit diagnostics. These tables are rebuilt atomically by `aggregate.py` and may be partial while the spectral producer is running.

`results/{world}_{parity}_m{m}.json` holds each complete HIGH rounded-vector polynomial census, the forced exterior carrier zeros below the primary cutoff, the three cutoff comparisons, and precision diagnostics. A result binds frozen source-vector bytes at job start. Its source-ground and parity-ground resolution flags are separate from its finite-polynomial isolation status. The primary object is always the even-restricted ground. A second odd result is produced when a resolved full ground belongs to odd parity; an even winner reuses the even artifact. Selected pilots also retain odd controls.

`METHOD.md` gives the formula, prediction, matching rules, and exact scope. `controls.json` records manufactured real, complex, negative-u, and parity controls. `low_bracket_validation_m300.json` validates degree-many LOW roots for all five relevant m300 parity targets using interval signs and exact rational bracket checks. That certificate concerns only frozen decimal-vector polynomials.

Run one vector:

```sh
PYTHONPATH=/workspace/conditioning_deps python roots/census.py spectra/vectors/zeta_m300.json --parity even
```

Run all available, resolved inputs, with bounded local worker processes:

```sh
PYTHONPATH=/workspace/conditioning_deps python roots/batch.py --workers 2
```

The streaming consumer is `watch.py --workers 2`. It consumes the full requested integer grid m=16,...,300 across zeta, DH, and planted worlds, and writes `watch_status.json`. Unresolved ground inputs remain explicit; no arbitrary cluster vector is selected. Arithmetic replay (`--repeat`) concerns the same supplied vector and must not be confused with the separate low/high source/eigenvector replay.

All work in this folder is an empirical finite-ground experiment. It makes no route state, D0, positivity theorem, RH, or exact-source certificate claim.

The adopted zeta-even continuation producer is frozen in `real_continuation_v1.py`, with exact code/review bindings in `continuation_adoption.json`. Every continuation result passes its own complete interval/degree proof for the supplied decimal polynomial; failures use full complex Flint isolation. Previous completed files are preserved. The displayed 180 digits are rendering precision; the declared root isolation target is 1e−165 in u.

The canonical complete LOW m300 interval reproducer is `reproduce_low_brackets_m300.py`. Its ordered, bounded substeps run in staging and publish only after all five polynomial degree/sign/bracket checks pass; see `low_bracket_reproducer_manifest.json`.

`PRECISION_SCOPE_ERRATUM.md` is authoritative for the frozen Cauchy diagnostic: sqrt(L)||delta c|| is real-axis and fixed-carrier only. The final `PRECISION_SCOPE_INVENTORY.json` binds raw files and supplies the off-axis growth correction. Neither quantity encloses exact-source eigenvector error; displayed 180 digits are not a claim of 180-digit physical accuracy.

Stored absolute source paths remain immutable provenance. Mutable analysis and LOW reproduction utilities use that path when available; if absent after packet relocation, they use `../spectra/vectors/<basename>` relative to this folder and require the original stored source SHA to match. Relocation does not rebind or alter any raw numerical result.

Final closure contains 1,095 required cases (855 even-primary and 240 winning-odd), plus 12 selected physical parity controls. `results/` additionally retains two manufactured controls, `synthetic_constant_even_m16.json` and `synthetic_constant_odd_m16.json`, tied to `synthetic_constant_m16.json`; these two are excluded from the scientific source-ground inventories. They are not stale source receipts.

`FINAL_AUDIT.json` reports `PASS_COMPLETE_GRID` with no missing or failed integrity checks. `PRECISION_SCOPE_INVENTORY.json` is complete and authoritative for the corrected diagnostic scope. Interval certificates concern supplied decimal-vector polynomials; exact-source eigenvectors and mathematical route status are not certified.
