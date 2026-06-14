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
same-unit `mu_K` budget?
```

Here "price" means the loss paid to preserve the structures needed by E5p:

```text
edge-control cost
PSD / nonnegative-hat cost
projection loss
negative signed ledger
uncertainty tax
tail / finite-ledger remainder
```

If a route's price is larger than the `mu_K` budget, the route is not merely
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
LP route gives a finite dual-clamp / certificate-gap interface;
S5C-LP is the final finite dual feasibility gate;
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
| S5C0 Route C | Build PSD-first hard-edge lift. | At `B_K=1`, PSD tax `2.93072`, `3.50596`, `3.96288`; ordinary tax is `1`. | surcharge confirmed, same-unit `mu_K` source absent. | `S5C0_SURCHARGE_CONFIRMED_MU_RATIO_OPEN` | Supply same-unit `mu_K` source or move to Route D. |
| S5C-LP final gate | Spectral/SOS dual clamp on the finite K-cell cone. | Budget-scale `gamma_cap=edge_scale` is infeasible for signed-triplet dictionary on `K=2,3,3.5`; K=2 remains infeasible with small `all` dictionary. Relaxed K=2 `10x` cap gives `eta=1.647`, `clamp=2.66093` vs edge scale `0.101393`; K=3/3.5 at `100x` still guard-fail with huge clamps. | Current executable finite witness family is red; route-level impossibility for every spectral/SOS witness remains open. | `S5C_LP_DICTIONARY_RED` | Either supply richer exact dual-cone basis or accept practical LP-family red signal and switch main effort to operator/prolate. |
| E5p raw-edge interval PSD | Certify direct raw-edge domination by supplied finite thresholds. | Arb interval full-space penalty cert passes for `K=2,3,3.5` with supplied `mu=(0.45,0.51,0.75)` and `tau=1e8`; min eigen lower bounds are about `0.0129205`, `0.0123293`, `0.0150617`. Same-unit bridge audit found no analytic `mu_K` source for these thresholds. | Finite raw-edge PSD is certified for supplied mu values, but analytic same-unit `mu_K` bridge is still missing. | `E5P_RAW_EDGE_INTERVAL_CERT_PASS_SUPPLIED_MU`; `E5P_BRIDGE_SOURCE_GAP` | Supply a repository analytic `mu_K` theorem in same `G/Q` normalization, or lower supplied thresholds to a proved budget. |
| Old Step32F lower-bound reuse | Reuse the certified `C=A-P = Dtheta + theta*Rkappa` LDL reserve as the edge budget. | Task 0A: the old object is a live exact rational LDL certificate, not the buried float Rayleigh artefact. Task 0B: it is not a free pre-edge reserve, since old `P` already contains the edge prime support. Old floors imply only `m_G >= 1.354e-4` (`primaryK11`) and `1.254e-5` (`controlK9`) in the old `L=3` self-cell, while forced raw edge `[3,6]` has `G`-opnorm about `1.10`. Current S5C cells are also different operators/normalizations. | The old engine is real and useful as an LDL pattern, but not as a ready raw-edge domination reserve; adding `m_old` to `mu_K` would require a new pre-edge ledger-support proof. | `TRACKB_REUSE_GAP_NOT_EDGE_OPERATOR`; `TRACKB_REUSE_GAP_CIRCULARITY_OR_LEDGER_SUPPORT`; nearest-cell `TRACKB_REUSE_FATAL_INSUFFICIENT_RESERVE` | Do not build a new external lift from this reserve; reuse only the penalty/LDL receiver pattern. |
| S5.1 (mollifier) | K-mollifier finite combo of edge-defect indicators. | Ansatz exists, but no inverse Dirichlet expansion / K-family second moment found locally. | Cannot revive S5.1 from current inputs. | `MOLLIFIER_GAP_NO_INVERSE_EXPANSION` | Do not spend until inverse expansion and off-diagonal moment are supplied. |
| Route D | Finite bad-mode / bad-region ledger plus tail bound. | Not run yet. | Fallback only if LP dual, Selberg-compatible lift, and mollifier route all fail. | `PARKED_FALLBACK_AFTER_D1_D2_D3` | Run only after the three atlas-derived routes are explicitly exhausted. |

## Missing Number

The decisive proof-relevant comparison is:

```text
budget_slack_K  =  mu_K -  d_K  -  transfer_guards_K
```

where:

```text
p_K = sup edge-defect Rayleigh value over the admissible finite K-cell cone
d_K = inf dual magic-function clamp satisfying PSD/sign/boundary constraints
certificate_gap_K  =  d_K  -  p_K  -  finite_guards_K
```

The scalar `certificate_gap_K` is a finite LP/certificate slack.  It is useful
for checking the health of a dual witness, but it is not the analytic E5p
`mu`-budget.  The same-unit interface is fixed in
`docs/trackB/MU_BUDGET_INTERFACE.md`.

The old local Track B docs exposed only qualitative targets:

```text
epsilon_K = o(1/B_K)
epsilon_K <= C*K^(-c)
```

The LP reformulation replaces part of that ambiguity with a computable finite
certificate gap.  It does not prove the E5p budget fits.  If exact
optimization/guards collapse the certificate gap to zero, that is a negative
finite LP verdict.  If `budget_slack_K = mu_K-d_K-transfer_guards_K` is not established in the
same units, the E5p node remains open.

Current status:

```text
mu_K same-unit source: GAP
certificate_gap formula: COMPUTABLE_FORMULA_READY
numerical dual witness: OPEN
continuous/interval guards: GAP
```

## Decision Tree

```text
1. If S5C-LP finite dual feasibility is solved:
     compute certificate_gap_K = d_K - p_K - finite_guards_K.
     compute budget_slack_K = mu_K - d_K - transfer_guards_K only after
     a same-unit mu_K bridge is proved.

     if budget_slack_K > 0:
       Route C(LP) remains alive;
       build the PSD-first admissible lift from the dual witness.

     if budget_slack_K <= 0 or the same-unit bridge is missing:
       Route C(LP) is priced and does not fit;
       go to Route D only after checking no Selberg-compatible lift exists.

     if finite K is green but asymptotic sign-uncertainty forecast conflicts:
       stop and audit K -> infinity stability.

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

The immediate deliverable is the same-unit dual clamp and budget comparison:

```text
Outcome 1:
  budget_slack_K = mu_K - d_K - transfer_guards_K is positive
  -> build the PSD-first admissible lift.

Outcome 2:
  budget_slack_K is nonpositive or not same-unit, and Selberg/mollifier cannot rescue
  -> run Route D finite ledger or close Track B negatively after D.

Outcome 3:
  LP dual cannot preserve Fourier-self-dual / F2 sign structure
  -> close Track B negatively with full price accounting.

Outcome 4:
  finite LP is green but asymptotic tax forecast conflicts
  -> stop for K-to-infinity stability audit before analytic E5 claims.
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
1. Implement/solve S5C-LP finite spectral/SOS dual feasibility for d_K and
   certificate_gap_K, then compare mu_K-d_K-transfer_guards_K only through the same-unit interface.
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
docs/trackB/S5C_LP_FINITE_DUAL_FEASIBILITY.md
docs/trackB/S5C_LP_NUMERICAL_GATE.md
docs/trackB/TRACKB_SELBERG_ROUTE_B_REPAIR.md
docs/trackB/TRACKB_MOLLIFIER_S51_REVIVAL.md
docs/trackB/CODEX_HANDOFF_LP_SELBERG_MOLLIFIER.md
docs/trackB/TRACKB_REUSE_OLD_LOWER_BOUND.md
docs/RH_TRICK_ATLAS.md#11-sign-uncertainty-surcharge
/Users/emalam/Documents/GitHub/prowka-bot/Projects/math-arsenal/atlas/020-cohn-elkies-lp.md
/Users/emalam/Documents/GitHub/prowka-bot/Projects/math-arsenal/atlas/028-conrey-ghosh-mollifier.md
/Users/emalam/Documents/GitHub/prowka-bot/Projects/math-arsenal/atlas/009-selberg-extremals.md
```

## Status Dictionary

```text
PROVED: none
SKETCH: numerical price accounting for current Track B families; LP/S5C-LP dual-clamp formulation
OPEN: richer exact spectral/SOS witness basis; Route D finite ledger
REFUTED: current product lift, Route A signed-small-negative repair, Selberg-alone Route B rescue, current S5C-LP dictionary, old Step32F reserve as a free pre-edge raw-edge domination budget
ZERO_CONSISTENT: S3 closure bookkeeping
GAP: same-unit analytic mu_K source for supplied raw-edge thresholds (`E5P_BRIDGE_SOURCE_GAP`); same-unit mu_K vs d_K bridge; spectral/SOS witness existence; continuous/interval guards for LP dual; old Step32F certificate is not the current edge operator; old Step32F support is post-edge/mixed unless a new ledger proof separates pre-edge reserve; mollifier inverse expansion / second moment
```
