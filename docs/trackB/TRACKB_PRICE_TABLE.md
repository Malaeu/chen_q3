# Track B Price Table

Status: CONTROL_PANEL.  This is strategy/diagnostic documentation only: no
Lean proof, no Q3.Main change, no route mutation, and no RH-conditional input.

## Purpose

Track B is no longer asking:

```text
Does B2b maybe work?
```

The current question is sharper:

```text
Is there any admissible explicit-formula lift whose total price fits the
mu-budget?
```

Here "price" means the loss paid to preserve the structures needed by E5':

```text
edge-control cost
PSD / nonnegative-hat cost
projection loss
negative signed ledger
uncertainty tax
tail / finite-ledger remainder
```

If a route's price is larger than the `mu`-budget, the route is not merely
hard.  It is structurally dead for Track B.

## Current Compression

What used to be:

```text
B2b maybe works?
```

is now:

```text
product-lift family dead;
signed-small repair dead;
PSD-first route pays surcharge;
only exact mu-budget ratio and final finite-ledger fallback remain.
```

## Route Price Table

| route / gate | attempted move | measured price | budget status | verdict | next action |
| --- | --- | --- | --- | --- | --- |
| S3 closure | Check four-slot accounting identity. | max closure relative error `9.93e-17` at K=2, `3.47e-16` at K=3. | Not a proof budget; bookkeeping only. | `ZERO_CONSISTENT` | Keep as regression, not proof gate. |
| S4 product lift | Use `L=Mplus*F_v` as zero-side PSD object. | min hat `-1.68036`, `-2.67972`, `-2.44648`. | Fails PSD eligibility before budget. | `B2B_S4_FATAL_NOT_PSD_ELIGIBLE_FOR_CURRENT_LIFT` | Do not reuse this lift. |
| S5.1 Route A | Split into positive part minus small negative ledger. | negative/L1 for `L`: `0.499632`, `0.500130`, `0.500021`; for `E`: `0.508842`, `0.494477`, `0.506019`. | Negative part is about half the spectrum, not a small ledger tail. | `REFUTED_FOR_CURRENT_FAMILY` | Route A closed for this family. |
| Route B | Clip spectrum: `hat(L_proj)=max(hat(L),0)`. | Would remove budget-sized spectral mass. | PSD is repaired, but edge-control/projection-loss likely budget-sized. | `DEFERRED_BY_S5_NEGMASS_BUDGET_SIZED` | Do not run unless exact projection-loss budget is supplied. |
| S5C0 Route C | Build PSD-first hard-edge lift. | At `B_K=1`, PSD tax `2.93072`, `3.50596`, `3.96288`; ordinary tax is `1`. | surcharge confirmed, exact `mu_budget(K)` absent. | `S5C0_SURCHARGE_CONFIRMED_MU_RATIO_OPEN` | Supply exact `mu_budget(K)` or move to Route D. |
| Route D | Finite bad-mode / bad-region ledger plus tail bound. | Not run yet. | Last fallback after A/B/C are priced. | `PARKED_LAST_ROUTE` | Run only if we want final negative Track B closure. |

## Missing Number

The decisive missing object is:

```text
mu_budget(K)
```

The local Track B docs currently expose only qualitative targets:

```text
epsilon_K = o(1/B_K)
epsilon_K <= C*K^(-c)
```

They do not expose a single proof-grade numerical `mu_budget(K)` for
`K=2,3,3.5`.  That is why S5C0 stops at:

```text
S5C0_SURCHARGE_CONFIRMED_MU_RATIO_OPEN
```

instead of:

```text
S5C0_FATAL_UNCERTAINTY_TAX
```

## Decision Tree

```text
1. If exact mu_budget(K) is supplied:
     compute tax / mu.

     if tax / mu > 1:
       Route C = S5C0_FATAL_UNCERTAINTY_TAX
       go to Route D or close Track B after D.

     if tax / mu <= 1:
       Route C remains alive;
       construct an actual PSD-first lift with edge-control.

2. If exact mu_budget(K) is not supplied:
     do not pretend Route C is green or fatal.
     run Route D finite ledger as the last fallback.

3. If Route D also exceeds budget:
     output B2B_FATAL_NO_ADMISSIBLE_LIFT_FOUND
     Track B explicit-formula-lift families are exhausted.
     Track A / prolate Connes-Consani becomes the main route.
```

## What We Want Now

The immediate deliverable is not another trick atlas.  It is one of two
decisive outcomes:

```text
Outcome 1:
  exact mu-budget shows Route C tax fits
  -> build the PSD-first admissible lift.

Outcome 2:
  exact mu-budget or Route D shows the price does not fit
  -> close Track B negatively with full price accounting.
```

Either outcome is useful.  The bad outcome would be ambiguity:

```text
tax known, budget unknown, no fallback run
```

because that leaves Track B stuck in a non-decision.

## Current Recommendation

Unless an exact `mu_budget(K)` is immediately available, run Route D as a
bounded final fallback:

```text
finite bad modes / regions
explicit tail bound
mu-book entry
```

Route D should not try to rescue the old product lift.  It should answer one
binary question:

```text
Can the remaining finite/tail defect be made smaller than the Track B budget?
```

If no, Track B is closed with high-quality negative knowledge.

## Source Files

```text
docs/trackB/VERDICT_B2B.md
docs/trackB/S4_ZERO_SIDE_ELIGIBILITY.md
docs/trackB/S5_NEGATIVE_MASS_LEDGER.md
docs/trackB/S5C0_TAX_PREFLIGHT.md
docs/trackB/b2_uncertainty_tax_preflight.md
docs/RH_TRICK_ATLAS.md#11-sign-uncertainty-surcharge
```

## Status Dictionary

```text
PROVED: none
SKETCH: numerical price accounting for current Track B families
OPEN: exact mu_budget(K), Route D finite ledger
REFUTED: current product lift, Route A signed-small-negative repair
ZERO_CONSISTENT: S3 closure bookkeeping
GAP: final tax/mu ratio for Route C
```
