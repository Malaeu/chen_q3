# OperatorStaticSchurStabilityGate Goal Addendum

Append these requirements to the next `/goal Run OperatorStaticSchurStabilityGate for Route B TwoLevelSpectralLadder`.

Status: diagnostic only. No RH claim. No Phase 2. No formula or packet-definition changes.

## O2+ Parity-Zero Structural Judge

Run first at every anchor. This is a free structural/instrumentation check.

Facts to use:
- `T` preserves parity.
- `k1` and `k2_even` are even.
- `k2_odd` is odd.
- In exact arithmetic the `(k1,k2_odd)` and `(k2_even,k2_odd)` entries of `G`, `K_schur`, and `S0` are zero.

Required reports:
- `abs(S0_{k1,odd}) / ||S0||`
- `abs(S0_{even2,odd}) / ||S0||`

Registered threshold:
- both values must be `<= 1e-25` as numeric floor.

Failure code:
- `PARITY_CONTAMINATION`

If violated:
- Treat as instrumentation failure.
- Stop before interpreting any drift.

Exploit the block structure:
- `S0 = (2x2 even block) direct_sum (1x1 odd block)`.
- Report odd scalar `S0_oo`.
- Report `eig(even 2x2)`.
- Report `Delta_eff = S0_oo - eig1(even 2x2)` separately.
- Expected ordering: second level is odd, matching saved `parity(xi2) = -1`.

Alignment note for O2:
- The `V_n` basis is nested in `N`.
- Embed `N_low` packet vectors into `N_high` by zero-padding.
- Then run the 3x3 Procrustes alignment.

## O3+ Dimensionless Shape Invariants

Add scale-free theorem-facing invariants:
- `theta2/theta1` across `N` per `lambda_sq`.
- `theta3/theta1` across `N` per `lambda_sq`.

Registered Case-B signature:
- ratio drift from `N=90` to `N=120` must be at least `10x` smaller than raw `theta` drift.

Report:
- raw `theta` drift.
- ratio drift.
- whether the `10x` Case-B signature holds.

## O2++ Geometric N-Model

This replaces the rejected p~1 scalar model.

For aligned `S0` entries and `eig(S0)` compute:
- `rho = drift(60->90) / drift(90->120)`.

Registered:
- `rho >= 3` indicates exponential-class convergence.

If registered condition holds:
- Geometric extrapolation:
  `X_inf = X_120 + drift(90->120)/(rho - 1)`.
- Report residual.
- Label it `FIT_NOT_LAW`.

Do not resurrect the old p~1 scalar law.

## O1+ Fresh `(12,120)` Anchor Acceptance Test

If the gate buys a fresh `(lambda_sq,N)=(12,120)` anchor, acceptance requires both:
- parity-zero judge passes with the `<= 1e-25` threshold;
- deflated-vs-direct agreement is at least `25` digits, matching the standard reached at `(13,120)`.

Failure:
- If parity-zero fails, stop with `PARITY_CONTAMINATION`.
- If solver agreement fails, stop with the appropriate Schur solver/agreement failure code before interpreting drift.
