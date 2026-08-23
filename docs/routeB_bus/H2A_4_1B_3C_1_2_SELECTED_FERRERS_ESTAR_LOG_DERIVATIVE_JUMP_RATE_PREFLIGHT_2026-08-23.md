# H2A.4.1B.3C.1.2 — selected Ferrers E-star log-derivative / jump rate preflight (READ-ONLY MATH)

```yaml
PRIMARY: H2A_4_1B_3C_1_2_SELECTED_FERRERS_ESTAR_LOG_DERIVATIVE_JUMP_RATE_PREFLIGHT
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex unavailable
TASK: verdict 2467a3e3 — CODEX DIRECTIVE (REQ-2026-08-22-V)
MODE: READ_ONLY_MATH
LEAN_EDIT: false
ARISTOTLE_USED: false
NUMERICS_USED: false
BASE_HEAD: 2467a3e3800fc1d62aac79816cf457ceb0a9b2d7

OUTCOME_CODE: SEAM_BUDGET_SUBCRITICAL_INTERIOR_MULTIPLICATIVE_BOUND_OPEN

DISK_OBJECTS_USED:
  - "E_star (D0KTrialStage2.lean:24): E_star(h)(u) = sqrt(u) * sum'_{n>=1} h(n*u); window restriction to I_m = [lambda^-1, lambda]"
  - "selectedFerrersEStarMainCount (G6N1SelectedFerrersEStarWindowMainError.lean:50): floor(lambda_k/u) — dynamic active-dilation count"
  - "selectedFerrersEStarWindowMainError (same file:55): sqrt(u)-weighted finite sum of (sourceScale*prolateCombination((n+1)u) - 4*cylinderTarget((n+1)u))"
  - "L73.3 bound: per-term C0 packet rate C/lambda^2 (F72.6) summed over the dynamic count gives C/(lambda*sqrt(u)) — PROVED"
  - "Satz9SourceData.flux (G6N1Satz9SourcePackageInterface.lean:92): exact divergence-form ODE ((lambda^2-x^2)*p')' = ((2*pi*lambda*x)^2 - theta)*p on Ioo(-lambda, lambda)"
  - "parabolicCylinderD_zero_projectArgument (G6N1SelectedFerrersDirectCylinderRate.lean): D0(projectCylinderArgument x) = exp(-pi*x^2)"
  - "schedule: lambda_k = sqrt(k+2), gamma_k = 2*pi*lambda_k^2, m_k = N_k = k+2, L_k = log m_k = 2*log(lambda_k)"

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## EXACT OBJECTS

For degrees `j = 0, 4` on the selected window, with the precommitted schedule:

```text
e_(j,k)(x) = centerAnchorScalar_j(k) * selectedMode_(j,k)(x) - parabolicCylinderTarget_j(x),
```

on `x in [-lambda_k, lambda_k]`, no new family, no fitted scalar.  The
factor-four combined packet error on the multiplicative window is the literal

```text
EStarError_k(u) = sqrt(u) * sum_{n=1..floor(lambda_k/u)}
    ( sourceScale_k * prolateCombination((n)u) - 4 * cylinderTarget((n)u) )
  - (Gaussian target tail beyond the carrier, L73.4 object)
```

(the disk splits main sum and tail; the prolate carrier is hard-cut at
`|x| = lambda_k`, the Gaussian target is not).

**Structural identity used throughout (elementary, verified by chain rule):**
the log derivative commutes with `E_star` up to seams.  With `t = log u` and
`(M h)(x) := (1/2) * h(x) + x * h'(x)`:

```text
d/dt [ sqrt(u) * h(n*u) ] = sqrt(u) * (M h)(n*u).
```

Hence distributionally on the log window:

```text
D_t EStarError_k = E_star-type sum of (M e_proto) (interior density)
                 + sum_{r=1..floor(lambda_k^2)} jump_(k,r) * delta_(t_(k,r)),
  t_(k,r) = log(lambda_k / r),
```

where the seams are exactly the carrier cuts `r*u = lambda_k`, and the jump of
the `r`-th term is the carrier-edge value of the prolate side only (the
Gaussian target side is smooth across the seam):

```text
jump_(k,r) = sqrt(lambda_k / r) * sourceScale_k * prolateCombination(lambda_k).
```

Seam count on the window: `r` ranges to `floor(lambda_k / u)` at `u =
lambda_k^-1`, i.e. up to `lambda_k^2 = m_k` seams.  All endpoints and every
seam are enumerated by this formula; there are no others (the only
discontinuities of the summand family are the carrier cuts).

## TEST A — EXACT CENTER-NORMALIZED ODE DEFECT

Subtracting the two exact equations (no asymptotic notation):

- prolate side (`Satz9SourceData.flux`, exact):
  `((lambda^2 - x^2) * p')' = ((2*pi*lambda*x)^2 - theta) * p`;
- cylinder side (`D_nu` equation at the project argument `y = 2*sqrt(pi)*x`,
  exact): `T'' = (4*pi^2*x^2 - 2*pi*(2*nu+1)) * T` for `T(x) = D_nu(2*sqrt(pi)*x)`.

For `e = s*p - 4T` (center-anchored, `s = centerAnchorScalar`):

```text
((lambda^2 - x^2) * e')'
  = ((2*pi*lambda*x)^2 - theta) * e  +  F(x),

F(x) = 4 * [ ((2*pi*lambda*x)^2 - theta) * T(x)
             - ((lambda^2 - x^2) * T'(x))' ]
     = 4 * [ (4*pi^2*(lambda^2 - 1)*x^2 - theta + 2*pi*(2*nu+1)*lambda^2)
              * T(x) * (1 + exact lower-order terms)
             + (x * T'(x))' - lambda^2*0 ... ]   (exact polynomial-in-x
                                                 coefficients times T, T', T'')
```

Exact initial data at the center: `e(0) = 0` (the center anchor is an exact
value match — SOURCE_INTERFACE_AUDIT of verdict 2467a3e3), `e'(0) = 0`
(parity of both sides).  The forcing `F` is an explicit combination of `T`,
`T'`, `T''` with polynomial coefficients — Gaussian-decaying, fully explicit,
no O-terms.

**Assessment.**  On the oscillatory zone `|x| <= x_turn = O(1)` (turning point
of the cylinder operator at fixed degree), the Volterra representation from
exact zero initial data gives a genuine first-derivative estimate at cost
comparable to a Gronwall lemma — no spectral gap needed.  On the tail zone
`x_turn < |x| <= lambda`, the potential `(2*pi*lambda*x)^2 - theta` is
positive and large, the frozen-coefficient growing solution scales like
`exp(+integral of sqrt(V)/(lambda^2-x^2)-weight)`, and a raw Volterra bound
inflates by exactly the reciprocal of the Gaussian decay of the solutions:
absolute-value iteration is USELESS there.  A weighted energy
`E(x) = (lambda^2-x^2)*|e'|^2 + (V - theta)*|e|^2`-type functional with the
divergence-form weight is the standard repair; its monotonicity defect is
explicit and integrable, but this is a NEW theorem-sized analysis, not a
citation.  Verdict for Test A: the route is structurally sound and cheap in
the oscillatory zone, OPEN (new analysis) in the tail zone.  No new spectral
gap is assumed anywhere.

## TEST B — DIFFERENTIATED-KERNEL ROUTE

The Mathieu integral identities §2.333 (4)/(5) are source-verified (3C.1.1).
The spheroidal analogues would live in §3.32–3.33 (integral relations between
cylinder and sphere functions); those sections were NOT read in 3C.1.1 and
are NOT verified now — per the directive, an analogy with the Mathieu formula
is not an import.  Therefore the differentiated-kernel route currently has no
source-verified spheroidal kernel identity and cannot be marked green.

**Exponent bookkeeping of the route (recorded, conditional).**  In the
dimensionless variable, differentiating the kernel costs one factor of the
large parameter's square root (`kernel argument ~ sqrt(gamma)`), so the raw
dimensionless derivative remainder would be `O(gamma^(-3/4 + 1/2))`,
normalized `O(gamma^(-1/2))`.  The physical derivative then RECOVERS the loss
through the chain rule (`d/dx = (2*gamma)^(-1/2) * d/dz` at fixed window
map): expected physical C1 remainder

```text
sup |e'(x)| = O(gamma^(-1)) = O(lambda^(-2))  — same order as the C0 rate.
```

This cancellation (kernel loss `gamma^(+1/2)` versus chain-rule gain
`gamma^(-1/2)`) is the reason the route is worth pursuing at all.  It is a
PLAUSIBLE TARGET, not a proved rate.

## TEST C — SEAM LEDGER

Exact jump (derived above, including the square-root E-star prefactor and the
center-anchored edge value):

```text
jump_(k,r) = sqrt(lambda_k / r) * s_k * prolateCombination(lambda_k),
|s_k * prolateCombination(lambda_k)|
  <= 4 * |cylinderTarget(lambda_k)| + C/lambda_k^2     (F72.6 C0 rate at the edge)
  <= C' / lambda_k^2                                    (the Gaussian edge value
                                                        exp(-pi*lambda_k^2) is
                                                        absorbed into C').
```

Strongest source-derived bound on the seam mass:

```text
sum_{r=1}^{m} |jump_(k,r)|^2
  <= (C'/lambda^2)^2 * lambda * sum_{r=1}^{m} 1/r
  =  C'^2 * H_m * lambda^(-3)
  ~  C'^2 * L / m^(3/2).
```

This uses the harmonic sum exactly, NOT (number of seams) * (largest jump):
the largest jump is `r = 1` with `|jump|^2 ~ lambda * C'^2/lambda^4 =
C'^2/m^(3/2)`, and `m` seams times that would give `C'^2/sqrt(m)` — a loss of
`m/L` against the harmonic ledger.  Both numbers are carried to Test E.

## TEST D — FINITE FOURIER CONVERSION

Mode-weighted energy on `CCMModeFinite N_k`, exact interval length `L_k`,
orthonormal modes `V_n = L^(-1/2) * exp(2*pi*i*n*t/L)`.

**Jump part.**  A jump `J` at `t_0` contributes `n^2*|c_n|^2 =
(L/(4*pi^2)) * |J|^2 * (1 + smooth remainder)` per mode; for the seam family
the phased sum enters:

```text
sum_{|n| <= N} n^2 |c_n(jump part)|^2
  = (L/(4*pi^2)) * sum_{|n| <= N} | sum_r jump_(k,r) * e(n * t_(k,r) / L) |^2.
```

The seam phases `t_(k,r)/L = log(lambda/r)/L` have minimal spacing
`log(1 + 1/r)/L ~ 1/(r*L)`, worst case `delta ~ 1/(m*L)`.  A
Montgomery–Vaughan-type nonharmonic large sieve gives the factor
`(2N + delta^(-1)) = O(m*L)`:

```text
jump mode-weighted energy (SIEVE)
  <= C * L * (m*L) * (L/m^(3/2)) = C * L^3 / sqrt(m).
```

The triangle alternative pays `N * (sum_r |jump_r|)^2 <= N * m * sum_r
|jump_r|^2 = O(m^2 * L/m^(3/2)) * L`-scale — worse than the sieve by `m/L`:

```text
jump mode-weighted energy (TRIANGLE) ~ C * L^2 * sqrt(m).
```

The triangle bound is recorded as a KILL BOUND only, exactly as the directive
requires.  Caveat named openly: the large sieve at these specific
logarithmic-lattice phases is classical mathematics but has NO disk instance
and no Mathlib instance; using it is a named external input.

**Interior part.**  By the commutation identity, the interior density is an
E-star-type sum of `(M e_proto)(n*u)` with `|M e_proto(x)| <= (1/2)*|e| +
|x*e'|`.  With the PROVED C0 rate and the OPTIMISTIC (Test B target, unproved)
physical C1 rate `|e'| <= C/lambda^2`:

```text
|M e_proto (x)| <= C * (1 + x) / lambda^2 .
```

Pointwise summation over the dynamic count (the only method on disk, L73.3
mechanics):

```text
|interior(u)| <= sqrt(u) * sum_{n <= lambda/u} C*(n*u)/lambda^2
             <= sqrt(u) * C * lambda^2/(2u) / lambda^2 = C / (2*sqrt(u)),
||interior||^2_{L2(I_m, d*u)} <= C^2/4 * integral_{1/lambda}^{lambda} u^{-1} d*u
             ~ C^2 * lambda / 4 = C^2 * sqrt(m) / 4,
interior mode-weighted energy ~ (L/(2*pi))^2 * C^2 * sqrt(m).
```

## TEST E — CRITICAL-RATE COMPARISON

All entries in the required unit `budget / (sqrt(m_k)/L_k^2)`:

| contribution | method | budget | ratio to threshold | verdict |
|---|---|---|---|---|
| seam (jump) part | harmonic ledger + LARGE SIEVE | `L^3/sqrt(m)` | `L^5/m -> 0` | **SUBCRITICAL** (margin `m/L^5`) |
| seam (jump) part | triangle over seams | `L^2*sqrt(m)` | `L^4 -> infinity` | supercritical — kill bound only |
| interior part | pointwise count sum + optimistic C1 `O(lambda^-2)` | `L^2*sqrt(m)` | `L^4 -> infinity` | supercritical by exactly `L^4` |
| interior part | with proved facts only (no C1 at all) | unbounded | — | not even formulable |

**Reading.**  (i) The seam budget is decisively subcritical once the sharp
nonharmonic Fourier inequality is used, and decisively supercritical under
the seam-count triangle — judge prediction P_DERIVATIVE_BUDGET_1 = 0.82 is
CONFIRMED by the arithmetic.  (ii) The interior budget FAILS by a
polylogarithmic factor `L^4` even under the most optimistic fixed-mode C1
rate `O(lambda^-2)` — so a fixed-mode C1 theorem alone cannot close the
E-star mode-weighted budget; judge prediction P_DERIVATIVE_BUDGET_2 = 0.93 is
CONFIRMED.  (iii) The pointwise dynamic-count summation is the culprit: it
treats the `~lambda/u` dilation terms with absolute values.  Closing the
`L^4` gap requires a multiplicative inequality that sees cancellation across
dilations — a Mellin/zeta-critical-line L2 mechanism (`E_star` acts as a
`zeta(1/2+i*tau)` multiplier under Mellin–Plancherel on the half-line;
windowing and the finite count are the honest obstacles), a Hardy-type
dilation operator bound, or genuine sign oscillation of `e'` across the
carrier.  None of these exists on disk.  This is exactly the judge's
LIKELIEST_FAILURE (MULTIPLICATIVE_DILATION_OPERATOR_OR_SEAM_LARGE_SIEVE_GAP),
with the refinement that the SEAM half of that gap is benign (sieve is
classical and the margin is power-of-m) while the INTERIOR half is the real
wall (polylog gap, needs structure, not just a citation).

## OUTCOME AND MINIMAL MISSING OBJECTS

`SEAM_BUDGET_SUBCRITICAL_INTERIOR_MULTIPLICATIVE_BOUND_OPEN`

Ranked minimal missing inputs for a green source-rate contract:

```text
M1 (the wall): a multiplicative dilation operator bound for the interior
    density — an estimate of || sum_{n <= lambda/u} (M e)(n*u) ||_{L2(window, d*u)}
    that beats the pointwise count by more than L^2, e.g. via windowed
    Mellin/zeta L2 mechanics or proved oscillation of M e.
M2: the fixed-mode physical C1 rate O(lambda^-2) itself (Test A tail-zone
    weighted energy, or Test B with a source-verified spheroidal kernel
    identity from §3.32–3.33 — unverified sections, next acquisition candidate).
M3: the nonharmonic large sieve at the logarithmic seam lattice (classical;
    no disk/Mathlib instance; needed only for the seam half, which it closes
    with margin m/L^5).
```

Candidate-representation update:

```yaml
R1_PROJECT_ODE_FLUX_PLUS_MULTIPLICATIVE_ENERGY:
  kill_power: 10/10
  estimated_cost: 6/10   # raised from 5: tail-zone weighted energy is real
                         # analysis; M1 remains outside this route's scope
R2_DIFFERENTIATED_SOURCE_KERNEL_PLUS_SEAM_LARGE_SIEVE:
  kill_power: 9/10
  estimated_cost: 7/10   # unchanged; blocked on unverified §3.32–3.33 identity
NOTE: >-
  Neither route contains M1.  M1 is representation-independent: any interior
  estimate must cross the dilation sum.  The seam/sieve half (M3) belongs to
  R2's ledger and is benign.
```

## FORBIDDEN CHECK

```yaml
selected_schedule_changed: no (lambda_k = sqrt(k+2), gamma_k = 2*pi*(k+2) used as precommitted)
source_row_or_center_anchors_changed: no
factor_four_or_rayleigh_shift_changed: no
admitted_lean_files_touched: no
lean_written_or_aristotle_submitted: no
numerics_in_cofinal_quantifier: none (all ledgers are symbolic in m, L)
seam_count_times_max_jump_as_positive_route: no (recorded as kill bound only)
interior_C1_conflated_with_distributional_derivative: no (the commutation
  identity separates interior density from seam deltas explicitly)
```

## PREDICTION CHECK

```text
P_DERIVATIVE_BUDGET_1 = 0.82: CONFIRMED — sieve subcritical (L^5/m), triangle
  supercritical (L^4).
P_DERIVATIVE_BUDGET_2 = 0.93: CONFIRMED — optimistic C1 still leaves L^4 on
  the interior; fixed-mode C1 alone cannot close the budget.
P_DERIVATIVE_BUDGET_3 = 0.68: PARTIALLY CONFIRMED — the ODE/flux route does
  yield a cheap derivative estimate in the oscillatory zone and plausibly the
  full C1 after a tail-zone weighted energy, but the multiplicative E-star
  operator inequality (M1) is confirmed as a separate, unavoidable input.
LIKELIEST_FAILURE (multiplicative dilation operator or seam large sieve gap):
  OBSERVED, with the split refined: seam/sieve half benign, interior
  multiplicative half is the wall.
```

SUCCESS_CODE_RETURNED: SEAM_BUDGET_SUBCRITICAL_INTERIOR_MULTIPLICATIVE_BOUND_OPEN
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
