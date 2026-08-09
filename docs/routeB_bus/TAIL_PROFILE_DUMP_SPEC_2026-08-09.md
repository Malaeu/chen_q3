# SPEC ONLY — `tau` tail profile and off-head coupling row sums — 2026-08-09

Status: preregistered diagnostic specification only. No computation was run and no result is asserted here.

## Source lock and fixed choices

```yaml
cell_m: 13
lambda: sqrt(13)
phase1_generator: docs/routeB_bus/phase1_scripts/ccm_control_cell_penalty.py
phase1_sha256: 1be57db69683652ed4f6d56dba6fc3b70c186f429fbb7f5bef978cd84f08ed0d
tau_definition_lines: 150-201
head_sizes: [60, 120, 240]
shell_multiplier: 2
precision_dps: [180, 360]
arithmetic: python-flint/Arb intervals
adaptive_reoptimization: forbidden
post_result_schedule_changes: forbidden
```

The literal entry is the pinned Phase-1 expression

```text
tau(n,m) = W02(n,m) - WR(n,m) - Prime(n,m).
```

No profile, normalization, prime-power list, cell, or bin boundary may be changed after seeing values.

## Index sets

For each head size `H` in `{60,120,240}`, define

```text
I_H = { n in Z : |n| <= H }
S_H = { m in Z : H < |m| <= 2H }.
```

`S_H` is the preregistered next dyadic off-head shell. This spec does not claim that one shell equals the infinite tail.

For row `n`, compute the interval enclosure

```text
R_H(n) = sum_{m in S_H} |tau(n,m)|.
```

All absolute values and sums are Arb enclosures. Retain 180- and 360-dps outputs and require overlap for every reported aggregate.

## Required dump A — entry decay

For every evaluated `(n,m)`, retain enclosures for:

- `|tau(n,m)|`;
- `|n-m|` and `|n+m|`;
- signs of `n` and `m`;
- parity channel induced by `tau(i,j) ± tau(i,-j)`.

Use fixed dyadic distance bins

```text
[0,1], [2,3], [4,7], [8,15], [16,31],
[32,63], [64,127], [128,255], [256,511], [512,1023].
```

For each nonempty bin, report count, interval maximum, interval sum, and interval mean. Empty bins remain explicit.

## Required dump B — off-head row sums

For each `H`, report `R_H(n)` for:

1. every common core row `|n| <= 60`;
2. boundary rows `n in {±H, ±(H-1)}`;
3. the head-wide maximum over `n in I_H`.

Registered comparable core statistic:

```text
C_H = max_{|n| <= 60} R_H(n).
```

Also report core median and the fixed quantiles `0.50`, `0.90`, `0.99`; interval order ambiguity must remain explicit rather than resolved by midpoints.

## Falsifier and verdict classes

The intended tail-decoupling observation is falsified if the comparable core row sums are non-decaying with head size. Use enclosure separation only:

```text
TAIL_ROW_SUM_DECAY:
  upper(C_120) < lower(C_60)
  and upper(C_240) < lower(C_120)

TAIL_ROW_SUM_NONDECAYING:
  lower(C_120) >= upper(C_60)
  or lower(C_240) >= upper(C_120)

TAIL_ROW_SUM_UNRESOLVED:
  otherwise.
```

Boundary-row and head-wide maxima are diagnostics and cannot overturn the registered common-core verdict; report them separately.

No verdict class proves an infinite-tail bound. `TAIL_ROW_SUM_DECAY` is a finite-shell observation; `TAIL_ROW_SUM_NONDECAYING` kills only the proposed decay heuristic at these fixed heads.

## Eventual output contract — if separately authorized

The future run, if authorized, must produce:

- one JSON file containing all raw interval endpoints, source hashes, precision, timings, and overlap checks;
- one Markdown report containing the fixed tables and verdict;
- two independent implementations or one implementation with an independently coded recomputation of the aggregates;
- `CERT_NOT_FOUND` if any required enclosure or cross-check cannot be produced, with no tuning.

This specification authorizes no run, no Lean generation, and no route-state change.

## Decision record

- **Развилка:** infer tail decoupling from selected entries versus measure a registered row-sum object.
- **Выбрали:** literal `tau` entry dump plus comparable common-core off-head shell sums at heads 60/120/240.
- **Почему:** a row sum tests aggregate coupling that pointwise entry decay can hide.
- **Что отвергли и почему:** adaptive shell/profile selection is rejected because it would tune the diagnostic after seeing results; an infinite-tail claim is rejected because only one dyadic shell is measured.
- **Техника:** pinned Phase-1 generator, Arb enclosures, precision doubling, fixed bins.
- **Следующий ход:** none until an explicit run authorization; N=480 remains on hold.
- **Адреса:** source lock above; `phase1_scripts/ccm_control_cell_penalty.py:150`.
- **Чей вердикт и аргумент:** owner-requested falsifier; non-decaying off-head row sums would invalidate the proposed finite-head decoupling heuristic.

Boundaries: `CHALLENGER_NOT_RH`; `BUS_010 VOID`; `GOAL_055 HOLD`; no promotion; `PX_RH_CLAIM NOT_MADE`.
