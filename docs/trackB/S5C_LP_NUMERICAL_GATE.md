# Track B S5C-LP Numerical Gate

Status: DIAGNOSTIC_RED(current finite spectral/SOS dictionary).  This is a
finite numerical gate only: no Lean proof, no Q3.Main change, no route
mutation, and no RH-conditional input.

## Implementation

Added executable mode:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py s5clp --help
```

The mode reuses the current K-cell packet matrices and tests a finite
positive-definite spectral/SOS dictionary:

```text
P_lift - P_edge + eta*G >= 0
P0_lift - P0_edge <= gamma*G
```

after `ker Q` projection and `G` normalization.

Important engineering detail:

```text
shifted packet matrices are cached once per K
```

so the gate is no longer dominated by repeated B-spline matrix construction.

## Main Strict Gate

Command:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py s5clp \
  --K 2 3 3.5 --schedule stable \
  --lift-family signed-triplet \
  --num-centers 5 --widths 0.5 1.0 2.0 \
  --p0-na 201 --max-iter 60 --tol 1e-7 --top 6
```

This uses:

```text
gamma_cap = edge_defect_opnorm_scale
eta_green_tol = 1e-6
```

Results:

| K | ell | basis | edge scale | gamma cap | verdict | reason |
| --- | ---: | ---: | ---: | ---: | --- | --- |
| 2 | `0.75` | 75 | `0.101393` | `0.101393` | `B2B_LP_FATAL_LP_FAILED` | LP infeasible under budget-scale arch cap. |
| 3 | `0.75` | 75 | `0.108956` | `0.108956` | `B2B_LP_FATAL_LP_FAILED` | LP infeasible under budget-scale arch cap. |
| 3.5 | `1.375` | 75 | `0.236347` | `0.236347` | `B2B_LP_FATAL_LP_FAILED` | LP infeasible under budget-scale arch cap. |

K=2 control with the larger combined dictionary:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py s5clp \
  --K 2 --schedule stable --lift-family all \
  --num-centers 5 --widths 0.5 1.0 2.0 \
  --p0-na 201 --max-iter 60 --tol 1e-7 --top 6
```

Result:

| K | family | basis | edge scale | gamma cap | verdict |
| --- | --- | ---: | ---: | ---: | --- |
| 2 | all | 90 | `0.101393` | `0.101393` | `B2B_LP_FATAL_LP_FAILED` |

So the strict failure is not caused by omitting the two-point atoms at K=2.

## Relaxed-Cap Controls

The relaxed controls test whether the LP is intrinsically impossible or only
too expensive.

### 10x Gamma Cap

Command:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py s5clp \
  --K 2 3 3.5 --schedule stable \
  --lift-family signed-triplet \
  --num-centers 5 --widths 0.5 1.0 2.0 \
  --p0-na 201 --max-iter 60 --tol 1e-7 \
  --gamma-ratio-cap 10 --top 6
```

Results:

| K | gamma cap | eta | gamma | clamp `eta+gamma` | edge scale | verdict |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| 2 | `1.01393` | `1.64700` | `1.01393` | `2.66093` | `0.101393` | `B2B_LP_FATAL_POSITIVE_PRIME_SLACK_UNDER_COST_CAP` |
| 3 | `1.08956` | n/a | n/a | n/a | `0.108956` | `B2B_LP_FATAL_LP_FAILED` |
| 3.5 | `2.36347` | n/a | n/a | n/a | `0.236347` | `B2B_LP_FATAL_LP_FAILED` |

### 100x Gamma Cap

Command:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py s5clp \
  --K 3 3.5 --schedule stable \
  --lift-family signed-triplet \
  --num-centers 5 --widths 0.5 1.0 2.0 \
  --p0-na 201 --max-iter 60 --tol 1e-7 \
  --gamma-ratio-cap 100 --top 4
```

Results:

| K | gamma cap | eta | gamma | clamp `eta+gamma` | edge scale | min prime slack | verdict |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| 3 | `10.8956` | `3.92944` | `10.8956` | `14.8250` | `0.108956` | `-1.04e-4` | `B2B_LP_FATAL_GUARD_FAIL` |
| 3.5 | `23.6347` | `7.20583` | `23.6347` | `30.8405` | `0.236347` | `-2.05e-2` | `B2B_LP_FATAL_GUARD_FAIL` |

Even at 100x the finite edge scale, the candidate is nowhere near a usable E5'
budget.  The LP is not discovering a hidden budget-compatible dual clamp.

## Interpretation

This supports Fable's registered prediction:

```text
B2B_LP_FATAL is likely for the current dual/LP family.
```

But the scope is important:

```text
fatal for the current finite signed-triplet / small all-dictionary
spectral/SOS witness class;
not a theorem excluding every possible finite dual-cone certificate.
```

What the gate does establish:

```text
budget-scale gamma cap -> infeasible on K=2,3,3.5
10x cap -> K=2 feasible only with eta ~= 1.647 and clamp ~= 26x edge scale
100x cap -> K=3/3.5 still guard-fail with huge eta/gamma
```

Thus the current finite spectral/SOS dictionary fails for the same reason the
previous liftsearch failed: prime dominance and arch/cost control pull in
opposite directions.

## Verdict

```text
S5C_LP_DICTIONARY_RED
```

Route-level status:

```text
Track B dual/LP class: not formally dead yet.
Current executable finite witness family: red.
Next closure move, if we insist on Track B, must either:
  1. supply a richer exact spectral/SOS basis and rerun s5clp, or
  2. accept this as the final practical LP-family red signal and move to the
     operator/prolate route.
```

## Status Dictionary

```text
PROVED: none
SKETCH: finite numerical S5C-LP dictionary gate
OPEN: route-level impossibility for all possible spectral/SOS witnesses
REFUTED: current signed-triplet/all small spectral-SOS dictionary at budget scale
ZERO_CONSISTENT: S3 bookkeeping remains the closure regression
GAP: exact richer dual-cone basis or operator/prolate replacement
```
