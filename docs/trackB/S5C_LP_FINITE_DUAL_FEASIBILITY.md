# Track B S5C-LP: Finite Dual Feasibility Final Gate

Status: PLANNED_FINAL_GATE plus DIAGNOSTIC_RED(current executable finite
dictionary).  This is strategy/diagnostic documentation only: no Lean proof, no
Q3.Main change, no route mutation, and no RH-conditional input.

No new numerical run is recorded here.  This file turns the current mathematical
forecast into the next finite gate.

Numerical execution is recorded in:

```text
docs/trackB/S5C_LP_NUMERICAL_GATE.md
```

## Purpose

Track B has now priced the obvious external-lift routes:

```text
S4: product lift L=Mplus*F_v is not PSD eligible.
S5.1: signed-small repair has negative/L1 about 0.5.
S5C0: PSD-first hard-edge lift pays surcharge over ordinary Selberg tax.
```

The remaining question is narrow:

```text
Is there a finite-dimensional spectral/SOS dual clamp on the K-cell cone that
survives Q3 normalization?
```

This is the last honest LP test before declaring the current dual/LP class
fatal for E5p.

## Registered Prediction

Prediction:

```text
B2B_LP_FATAL is more likely than B2B_LP_CERT_READY.
```

Reason:

| pointer | local status | what it says |
| --- | --- | --- |
| S4 product lift | `B2B_S4_FATAL_NOT_PSD_ELIGIBLE_FOR_CURRENT_LIFT` | Multiplying by the Selberg/CLV receiver does not preserve zero-side PSD. |
| S5.1 signed repair | `S5_NEGMASS_BUDGET_SIZED` | The negative spectrum is order one, not a ledger tail. |
| S5C0 surcharge | `S5C0_SURCHARGE_CONFIRMED_MU_RATIO_OPEN` | PSD plus hard-edge control costs more than ordinary `1/B_K` in the finite tax instrument. |
| BCK-style sign uncertainty | route-design theorem/warning in atlas card 11 | Hard physical sign plus Fourier-side nonnegativity has an unavoidable uncertainty cost. |
| Sarnak/de Branges warning | negative warning only, not a route input | Natural too-strong positivity certificates for RH are known to fail; do not rebuild that route. |

The last two are not used as computational assumptions.  They explain why a
naive dual certificate is expected to fail and why the next gate must be finite
and cone-specific, not another scalar majorant.

## Survival Gap

There is one real gap through which Track B can still survive:

```text
finite K may admit a spectral/SOS witness even when the asymptotic hard-edge
tax predicts no uniform free lunch.
```

Therefore the witness is forbidden to be:

```text
CLV multiplication
ordinary Selberg scalar mask
spectral clipping without edge-control ledger
de Branges positivity route
Fourier-quasicrystal transfer
```

The witness must be:

```text
spectral / SOS / dual-cone certificate on the existing finite K-cell cone
```

Atlas source:

```text
007 Dual certificate / positivity cone
/Users/emalam/Documents/GitHub/prowka-bot/Projects/math-arsenal/atlas/007-dual-certificate.md

020 Cohn-Elkies LP framework
/Users/emalam/Documents/GitHub/prowka-bot/Projects/math-arsenal/atlas/020-cohn-elkies-lp.md
```

Unconditional input: the finite dual-certificate framework is UNCONDITIONAL.
The hard part is existence of the certificate and preservation of Q3
normalization.

## Gate Definition

Run on the current finite K-cell matrices for:

```text
K = 2, 3, 3.5
```

Use the current finite cone:

```text
C_K = Hermitian-square finite packet cone
      intersect ker Q boundary constraints
      with current support/bandlimit receiver normalization.
```

Primal:

```text
p_K = sup { edge_defect_K(v) : v in C_K, ||v||_G = 1 }.
```

Dual:

```text
d_K = inf { dual_clamp_K(W) :
            W is a spectral/SOS finite witness,
            W preserves zero-side PSD,
            W has the correct edge-defect sign,
            W satisfies boundary/cap normalization }.
```

Certificate gap:

```text
certificate_gap_K = d_K - p_K - finite_guards_K
```

Budget:

```text
budget_slack_K =
  mu_K - d_K - transfer_guards_K
```

Expanded same-unit diagnostic:

```text
usable_budget_slack_K =
  mu_K
  - d_K
  - closure_error_K
  - boundary_error_K
  - quadrature_error_K
  - finite_projection_error_K.
```

## Required Guards

The LP witness must be returned to the same four-slot Q3 bookkeeping:

```text
arch | zero_PSD | prime | boundary
```

Required checks:

| guard | pass condition | failure verdict |
| --- | --- | --- |
| PSD | sampled/finite zero-side matrix is PSD within tolerance | `LP_WITNESS_NOT_PSD` |
| sign | physical-side edge sign clamps the defect | `LP_WITNESS_SIGN_WRONG` |
| boundary | `Q_1,Q_2` boundary functionals stay within guard | `LP_WITNESS_BOUNDARY_FAIL` |
| closure | S3-style four-slot closure survives insertion | `LP_WITNESS_Q3_NORMALIZATION_FAIL` |
| finite certificate | `certificate_gap_K > guards` | `LP_GAP_NONPOSITIVE` |
| budget | `budget_slack_K > 0` after a same-unit `mu_K` bridge, with expanded guards paid if using `usable_budget_slack_K` | `BUDGET_SLACK_GAP` or `B2B_LP_FATAL` |

Forbidden LP-GREEN trap:

```text
B2B_LP_GREEN is forbidden as a closure of E5p.
It is at most a finite-LP signal. Closure requires:

  (i)  budget_slack_K >= 0 (same-unit), AND
  (ii) same-unit mu_K bridge proven (TRACKB_E5P_THEOREM.md obligation mu-normalization), AND
  (iii) penalty PSD cert mu_K*G_K - E_edge_K + tau_K*Q_K^T Q_K >= 0 (tau-PSD-cert).

Missing any one -> status = GAP, not GREEN.
```

## Verdicts

```text
B2B_LP_CERT_READY:
  budget_slack_K > 0 on the tested K values
  after a proved same-unit bridge
  and PSD/sign/boundary/closure guards all pass.

  Meaning:
    Track B remains alive.
    The finite witness becomes input for an analytic E5 lemma.

B2B_LP_FATAL:
  budget_slack_K <= 0
  or the witness breaks PSD/sign/boundary/Q3 normalization.
  If the same-unit mu_K bridge is missing, the correct status is GAP, not GREEN.

  Meaning:
    The current dual/LP class is dead for Track B.
    Move main effort to the operator-first/prolate route.

B2B_LP_CONFLICT:
  finite LP is green but the asymptotic sign-uncertainty forecast says the
  family cannot persist.

  Meaning:
    Stop and audit K -> infinity stability before claiming an E5 route.
```

## Relation To Prolates

If S5C-LP is fatal, do not interpret that as "no structure exists."  It means
the external dual/LP certificate class has failed.

The operator-first/prolate route is different:

```text
PSD is built into self-adjoint/spectral structure,
not bolted on by a separate Fourier-side nonnegativity constraint.
```

That is the reason it is not killed by the same hard-edge tax preflight.

## Status Dictionary

```text
PROVED: none
SKETCH: final finite LP/SOS gate statement; current finite dictionary red
OPEN: richer exact dual-cone witness basis; K -> infinity stability if green
REFUTED: naive CLV/product/signed-small Selberg lift classes; current signed-triplet/all small dictionary
ZERO_CONSISTENT: S3 remains the closure regression
GAP: same-unit mu_K vs d_K bridge; spectral/SOS witness existence and Q3-normalization survival
```
