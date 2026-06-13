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
LP route gives the computable mu-budget object;
Selberg alone does not undie Route B;
mollifier revival lacks inverse expansion / second moment inputs;
Route D is fallback only after LP/Selberg/mollifier fail.
```

## Route Price Table

| route / gate | attempted move | measured price | budget status | verdict | next action |
| --- | --- | --- | --- | --- | --- |
| S3 closure | Check four-slot accounting identity. | max closure relative error `9.93e-17` at K=2, `3.47e-16` at K=3. | Not a proof budget; bookkeeping only. | `ZERO_CONSISTENT` | Keep as regression, not proof gate. |
| S4 product lift | Use `L=Mplus*F_v` as zero-side PSD object. | min hat `-1.68036`, `-2.67972`, `-2.44648`. | Fails PSD eligibility before budget. | `B2B_S4_FATAL_NOT_PSD_ELIGIBLE_FOR_CURRENT_LIFT` | Do not reuse this lift. |
| S5.1 Route A | Split into positive part minus small negative ledger. | negative/L1 for `L`: `0.499632`, `0.500130`, `0.500021`; for `E`: `0.508842`, `0.494477`, `0.506019`. | Negative part is about half the spectrum, not a small ledger tail. | `REFUTED_FOR_CURRENT_FAMILY` | Route A closed for this family. |
| Route B | Clip spectrum: `hat(L_proj)=max(hat(L),0)`. | Would remove budget-sized spectral mass. Selberg exact edge tax is `1/B_K=1` in current run, but current lifted family has min hats `-1.68036`, `-2.67972`, `-2.44648`. | Selberg repairs scalar edge constant, not PSD/cone transport. | `SELBERG_REPAIR_NO_UNDIE_ROUTE_B` | Use Selberg only inside LP dual or after exact projection-loss budget. |
| S5C0 Route C | Build PSD-first hard-edge lift. | At `B_K=1`, PSD tax `2.93072`, `3.50596`, `3.96288`; ordinary tax is `1`. | surcharge confirmed, exact `mu_budget(K)` absent. | `S5C0_SURCHARGE_CONFIRMED_MU_RATIO_OPEN` | Supply exact `mu_budget(K)` or move to Route D. |
| S5C0 Route C (LP) | Cohn-Elkies LP dual on the finite K-cell cone. | `mu_budget_LP(K)=d_K-p_K`, where `p_K` is the primal worst edge Rayleigh value and `d_K` is the candidate/best dual clamp in the finite relaxation. | Formula is concrete; positive usable gap is not yet shown. | `COMPUTABLE_FORMULA_READY` | Build/solve dual feasibility wrapper around existing K-cell matrices. |
| S5.1 (mollifier) | K-mollifier finite combo of edge-defect indicators. | Ansatz exists, but no inverse Dirichlet expansion / K-family second moment found locally. | Cannot revive S5.1 from current inputs. | `MOLLIFIER_GAP_NO_INVERSE_EXPANSION` | Do not spend until inverse expansion and off-diagonal moment are supplied. |
| Route D | Finite bad-mode / bad-region ledger plus tail bound. | Not run yet. | Fallback only if LP dual, Selberg-compatible lift, and mollifier route all fail. | `PARKED_FALLBACK_AFTER_D1_D2_D3` | Run only after the three atlas-derived routes are explicitly exhausted. |

## Missing Number

The decisive object is now named:

```text
mu_budget_LP(K) = d_K - p_K
```

where:

```text
p_K = sup edge-defect Rayleigh value over the admissible finite K-cell cone
d_K = inf dual magic-function clamp satisfying PSD/sign/boundary constraints
```

The old local Track B docs exposed only qualitative targets:

```text
epsilon_K = o(1/B_K)
epsilon_K <= C*K^(-c)
```

The LP reformulation replaces that ambiguity with a computable gap.  It does
not claim the gap is positive yet.  If exact optimization/guards collapse the
gap to zero, that is a negative priced verdict, not a failure of bookkeeping.

Current status:

```text
mu_budget formula: COMPUTABLE_FORMULA_READY
numerical dual witness: OPEN
continuous/interval guards: GAP
```

## Decision Tree

```text
1. If the LP dual is solved:
     compute mu_budget_usable(K) = d_K - p_K - guards.

     if mu_budget_usable(K) > 0:
       Route C(LP) remains alive;
       build the PSD-first admissible lift from the dual witness.

     if mu_budget_usable(K) <= 0:
       Route C(LP) is priced and does not fit;
       go to Route D only after checking no Selberg-compatible lift exists.

2. Route B after Selberg:
     scalar edge constant is exact, but Route B is not undied because PSD/cone
     transport remains broken for the current lifted family.

3. Mollifier after card 028:
     finite ansatz exists, but current repo inputs do not contain the inverse
     expansion or off-diagonal moment formula. Treat as GAP, not rescue.

4. If Route D also exceeds budget:
     output B2B_FATAL_NO_ADMISSIBLE_LIFT_FOUND
     Track B explicit-formula-lift families are exhausted.
     Track A / prolate Connes-Consani becomes the main route.
```

## What We Want Now

The immediate deliverable is the LP dual budget:

```text
Outcome 1:
  LP gap mu_budget_usable(K) is positive
  -> build the PSD-first admissible lift.

Outcome 2:
  LP gap is nonpositive, and Selberg/mollifier cannot rescue
  -> run Route D finite ledger or close Track B negatively after D.

Outcome 3:
  LP dual cannot preserve Fourier-self-dual / F2 sign structure
  -> close Track B negatively with full price accounting.
```

Either outcome is useful.  The bad outcome would be ambiguity:

```text
tax known, budget unknown, no fallback run
```

because that leaves Track B stuck in a non-decision.

## Current Recommendation

Do not jump straight to Route D until the LP dual feasibility check is attempted.
Route D is now explicitly demoted to fallback after:

```text
D1 LP dual gap route
D2 Selberg-compatible lift / projection-loss route
D3 mollifier inverse-expansion route
```

Current recommendation:

```text
1. Implement/solve the finite LP dual wrapper for mu_budget_LP(K).
2. Keep Selberg as scalar edge-constant input inside that LP.
3. Do not spend on mollifier unless inverse expansion + moment formula appear.
4. Run Route D only after the LP route is priced.
```

## Source Files

```text
docs/trackB/VERDICT_B2B.md
docs/trackB/S4_ZERO_SIDE_ELIGIBILITY.md
docs/trackB/S5_NEGATIVE_MASS_LEDGER.md
docs/trackB/S5C0_TAX_PREFLIGHT.md
docs/trackB/b2_uncertainty_tax_preflight.md
docs/trackB/TRACKB_LP_REFORMULATION.md
docs/trackB/TRACKB_SELBERG_ROUTE_B_REPAIR.md
docs/trackB/TRACKB_MOLLIFIER_S51_REVIVAL.md
docs/trackB/CODEX_HANDOFF_LP_SELBERG_MOLLIFIER.md
docs/RH_TRICK_ATLAS.md#11-sign-uncertainty-surcharge
/Users/emalam/Documents/GitHub/prowka-bot/Projects/math-arsenal/atlas/020-cohn-elkies-lp.md
/Users/emalam/Documents/GitHub/prowka-bot/Projects/math-arsenal/atlas/028-conrey-ghosh-mollifier.md
/Users/emalam/Documents/GitHub/prowka-bot/Projects/math-arsenal/atlas/009-selberg-extremals.md
```

## Status Dictionary

```text
PROVED: none
SKETCH: numerical price accounting for current Track B families; LP formulation
OPEN: LP dual witness solve; Route D finite ledger
REFUTED: current product lift, Route A signed-small-negative repair, Selberg-alone Route B rescue
ZERO_CONSISTENT: S3 closure bookkeeping
GAP: continuous/interval guards for LP dual; mollifier inverse expansion / second moment
```
