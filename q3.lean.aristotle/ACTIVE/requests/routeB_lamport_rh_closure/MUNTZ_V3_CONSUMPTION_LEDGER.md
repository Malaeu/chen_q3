# Müntz v3 consumption ledger — Goal 039

Date: 2026-07-30
Project: `987ff124-3032-42e5-aa9f-24ceef69f62a`
Task: `472e126c-759f-4c69-8816-fa013ff740b2`
Lane: `CHALLENGER / NOT_RH`

## Exact consumed hypothesis

```lean
AnalyticOnNhd ℂ
  (fun s ↦ ∫ u in Set.Ioi (0 : ℝ), h u * (u : ℂ) ^ (s - 1))
  {s : ℂ | 0 < s.re}
```

from:

```lean
Measurable h
∀ u, u ∉ Set.Icc (0 : ℝ) b → h u = 0
LipschitzOnWith K h (Set.Ico 0 b)
```

Goal 039 closes this hypothesis locally in
`muntz_v3/RequestProject/MellinCompactSupportAnalyticity.lean`.

## Patch v1.1 — R6 template port

The local proof is the direct T4a port of
`docs/routeB_bus/muntz_r6/RequestProject/ConcreteAnalyticity.lean`:

| Repair | Checked implementation |
|---|---|
| R-i (`hbot`) | `LipschitzOnWith` bounds `‖h u‖` on `Ico 0 b` by `‖h 0‖ + K * |b|`; this is `K * b` on the intended `0 < b` branch and gives exponent `0` via `IsBigO.of_bound`/`isBigO_iff` |
| R-ii (`hlocal`) | `Measurable h` plus the same a.e. constant bound gives `LocallyIntegrableOn h (Ioi 0)` by `locallyIntegrableOn_const.mono`; the endpoint `u = b` is discarded as a null singleton |
| R-iii (`htop`) | unchanged compact-support eventual-zero proof at `atTop` |
| W | Mathlib `mellin` crosswalk uses only `smul_eq_mul` and `mul_comm`; `DifferentiableOn.analyticOnNhd` uses openness of `{s | 0 < s.re}` |

The bridge is 71 lines including import/open/namespace lines, builds without
holes, and needs no Aristotle iteration.

## K7 theorem classification

`H_mellin` below means exactly
`AnalyticOnNhd ℂ (Mellin h) H`, with `H = {w : ℂ | 0 < w.re}`.

| v3 declaration | Classification before Goal 039 | Exact live hypotheses |
|---|---|---|
| `one_mem_H` | `THEOREM_UNCONDITIONAL` | none |
| `mellin_one_eq_zero` | `THEOREM_CONDITIONAL(on hmass)` | `∫ v in Ioi 0, h v = 0` |
| `mellinDivOne_value_one` | `THEOREM_UNCONDITIONAL` | none |
| `mellinDivOne_of_ne` | `THEOREM_CONDITIONAL(on w ≠ 1)` | `w ≠ 1` |
| `mellinDivOne_of_ne_of_zero` | `THEOREM_CONDITIONAL(on hmass,w ≠ 1)` | `Mellin h 1 = 0`, `w ≠ 1` |
| `mellinDivOne_analyticOn` | `THEOREM_CONDITIONAL(on H_mellin)` | `H_mellin` |
| `zetaResidueFactor_value_one` | `THEOREM_UNCONDITIONAL` | none |
| `zetaResidueFactor_of_ne` | `THEOREM_CONDITIONAL(on w ≠ 1)` | `w ≠ 1` |
| `zetaResidueFactor_continuousAt_one` | `THEOREM_UNCONDITIONAL` | none |
| `zetaResidueFactor_analyticAt_one` | `THEOREM_UNCONDITIONAL` | none |
| `zetaResidueFactor_analyticOn` | `THEOREM_UNCONDITIONAL` | none |
| `zetaMellinPoleSub_analyticOn` | `THEOREM_CONDITIONAL(on H_mellin)` | `H_mellin` |
| `zetaMellinPoleSub_off_pole` | `THEOREM_CONDITIONAL(on hmass,w∈H,w≠1)` | `Mellin h 1 = 0`, `w ∈ H`, `w ≠ 1` |
| `zetaMellinPoleSub_value_one` | `THEOREM_UNCONDITIONAL` | none |
| `shiftedHalfPlane_isPreconnected` | `THEOREM_UNCONDITIONAL` | none |
| `continued_window_identity_of_analytic` | `THEOREM_CONDITIONAL(on H_mellin,hzero,hG,hRm,hRp,habs)` | exact six hypotheses in `Main.lean` |
| `continued_window_identity_raw_off_pole` | `THEOREM_CONDITIONAL(on hzero,hcont)` | `Mellin h 1 = 0`, continued identity |
| `continued_window_identity_pole_value` | `THEOREM_CONDITIONAL(on hcont)` | continued identity |

## Consumption result

| new declaration | Result |
|---|---|
| `mellin_compactSupport_analyticOnNhd` | discharges `H_mellin` from the exact measurable/support/Lipschitz hypotheses |
| `continued_window_identity_unconditional_mellin` | T5 with `H_mellin` discharged; retained window/tail analyticity and absolute-region identity remain explicit |
| `continued_window_identity_raw_off_pole_unconditional_mellin` | punctured raw-product corollary with `H_mellin` discharged |
| `continued_window_identity_pole_value_unconditional_mellin` | pole-value corollary with `H_mellin` discharged |

The unique open *hypothesis* recorded by the delivered v3 source was T4a,
and it is now closed locally.

## Plant inventory discrepancy

The delivered v3 archive contains no declarations named or semantically
implementing the requested explicit triangular-bump plants PL1–PL3. Its
`RequestProject/Main.lean` has 239 lines and ends at the two T5 corollaries.
Therefore PL1–PL3 cannot be “mechanically instantiated from the conditional
v3 layer”: there are no such declarations to instantiate.

This is a source-inventory mismatch, not a T4a failure. Goal 039 does not
assert `MUNTZ_V3_UNCONDITIONAL_LAYER_COMPLETE`. The existing v3 T5 and both
corollaries are consumed; the explicit plant package remains absent and must
be supplied by a separate theorem contract if the owner still requires it.

## Lane status

`T4A_CLOSED_LOCALLY`; Müntz v3 T5 consumption is Lean-checked; explicit
PL1–PL3 source declarations are absent; Route B remains
`CHALLENGER / NOT_RH`; Bus 010 remains void.

## 2026-08-02 addendum — exact-class supplier front assembled

The later exact-class execution has now discharged the four retained analytic
suppliers for the same measurable/Icc-zero/Ico-Lipschitz function class:

| Supplier | Checked declaration |
|---|---|
| `hG` | `gwin_analyticOnNhd_shiftedHalfPlane_v3Class` |
| `hRm` | `rminus_analyticOnNhd_shiftedHalfPlane_v3Class` |
| `hRp` | `rplus_analyticOnNhd_shiftedHalfPlane_v3Class` |
| `habs` | `habs_of_IccZero_IcoLipschitz` |

`MuntzV3ExactClassClosure.lean` consumes all four and exports:

- `continued_window_identity_v3Class`;
- `continued_window_identity_raw_off_pole_v3Class`;
- `continued_window_identity_pole_value_v3Class`.

The native v3 `habs` proof makes the semantic transport explicit: E-star core,
Mathlib/project Mellin conventions, `Icc`/`Ioo` null endpoints, and both tail
indicators.  The full standalone project builds 8050 jobs, the new production
files have no holes, and the four public declarations depend only on
`[propext, Classical.choice, Quot.sound]`.

Verdict: `HABS_SUPPLIER_DISCHARGED_FOR_V3_CLASS /
MUNTZ_V3_EXACT_CLASS_CONTINUATION_ASSEMBLED`.  This is not tail smallness,
cofinal convergence, detector closure, or RH.  Route B remains
`CHALLENGER / NOT_RH`; physical Bus 010 remains void.
