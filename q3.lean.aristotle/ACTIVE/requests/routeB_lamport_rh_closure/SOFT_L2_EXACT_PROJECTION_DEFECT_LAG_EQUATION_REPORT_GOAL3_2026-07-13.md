# Goal 3 — SOFT_L2 ExactProjectionDefectLagEquation

Status: `SOFT_L2_EXACT_PROJECTION_LEDGER_LOCKED / MEASURED / NOT_RH`

Authority: the verbatim materializations
`SOFT_L2_PRO_VERDICT_ROUND9_2026-07-13.md` and
`SOFT_L2_PRO_VERDICT_ROUND10_2026-07-13.md`.

## Exact theorem ledger

The full finite projection is

```text
S_(m,N)=Pi_sec Pi_(m,N) P_L,
E_proj(t)=<(I-S_(m,N))U_t q,T_full q>.
```

The exact lag equation is decomposed into the five required rows:

```text
E_win + E_Gal + E_sec + E_polemid + E_Arch.
```

The window term uses the exact fixed-window overlap

```text
D_(a,L)(t)=<Q_L U_t q,Q_L U_a q>,
D_(a,L)(t)!=0 => t*a>0 and |t-a|<L,
|D_(a,L)(t)|<=r_L(t)r_L(a).
```

Both shift plants pass: translating `q` relative to the fixed carrier changes
the window defect while preserving autocorrelation; translating `q` and the
complete carrier together leaves the full equation covariant.  The theorem
makes no smallness, compact-support, limiting-equation, or RH claim.

## Edge-mass measurement

`e_L(delta)` was evaluated at every registered depth for all seven available
cell/role series and plotted on a logarithmic scale.  On the high-precision
`N=120` family, the registered exponential-profile prediction is supported:

```text
m=12: 57.6429 < m=13: 60.9838 < m=14: 64.2522.
```

The `(53,120)` and `(101,120)` float64 inputs hit the approximately `1e-15`
edge cancellation floor, so all-cell monotonicity is unresolved rather than
claimed.  The independent `(13,120)` finite ground gives slope `61.1021`,
consistent with the portable value `60.9838`.

## Numerical lag ledger `(13,120)`

On `t/L=k/6`, `k=-6,...,6`, the runner records separately `LHS`, `mu*A(t)`,
the residual sum of defects, the window contribution computed from
`D_(a,L)`, and the remaining aggregate
`Galerkin+sector+Arch-window+pole/midpoint` contribution.

At `|t|=L`, the window row is approximately `-2.7237980474` and the aggregate
remainder is approximately `+2.7237980474`.  Thus the omitted aggregate is
not numerically small and has no compact-support signature on this finite
grid.  It is not labelled pure Galerkin: the available data do not separate
the Galerkin, sector, Arch, and correction rows, and a finite grid proves no
noncompact-support theorem.

At `t=0`, direct Weil-functional subtraction is cancellation-limited at
`5.7315e-36`; the saved high-precision matrix eigenpair supplies the exact
anchor `LHS(0)=mu*A(0)=mu` and residual zero.  Both values are retained and
distinguished.

## Phase-probe recoding

The existing verdict remains

```text
C2_PHASE_FREE
```

and the additional registered note is

```text
PHASE_SLOPE_EQUALS_LOG_LAMBDA_DIAGNOSTIC
```

The fitted slope is compared with `L/2=log(lambda)`.  The agreement is read
only as the half-shift signature and completion-gauge consistency, and is a
diagnostic input for the V1 parity-closure question.  It is not a parity
theorem, phase reconstruction, S2, or RH evidence.

## Closeout

```text
SOFT_L2_EXACT_PROJECTION_LEDGER_LOCKED
SOFT_L2_MEASUREMENTS_COMPLETE
C2_PHASE_FREE
PHASE_SLOPE_EQUALS_LOG_LAMBDA_DIAGNOSTIC
NOT_RH
BUS_010_CREATED=false
```

Bus 010 was not created.
