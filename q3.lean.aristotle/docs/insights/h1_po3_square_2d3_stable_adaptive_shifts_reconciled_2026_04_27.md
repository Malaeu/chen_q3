# `PO3-square.2d3`: stable adaptive shifts reconciled (2026-04-27)

## Verdict

The Proshka `PO3-square.2d3b5a` stable-adaptive-shift theorem is useful, but
it is a support packet, not a new active route node.

It restates the clean mechanism already recorded in
`h1_po3_square_2d3_adaptive_shift_constraints_2026_04_24.md`:

```text
future-slope-adapted shifts
  -> normalized rows converge to an exponential Vandermonde matrix
  -> small row errors force finite-difference/Hermite capture.
```

The later project corrections still dominate:

- endpoint orientation must be handled by the orientation-safe product theorem;
- right-edge later-base rows use bounded fractional exponents, not integer
  rows `p=0,1,...`;
- the right-edge bounded-separated certificate checks the actual fractional
  nodes `y_i=exp(t_i/(n-1))`;
- row capture is valid only after normalized shifted errors are small relative
  to the stable-projection conditioning.

Therefore this answer should not reset the active target back to generic
adaptive shifts.

## Useful theorem-shape retained

For the old one-sided shifted `A_k` rows, define

```text
Phi_{k,s}(x) = A_{k+s}(x) / A_k(x)
mu_k(s;xi)  = sum_{h=0}^{s-1} 1 / (N+k+2+h-xi).
```

If `lambda_k=Lambda_k(xi_k)` and shifts are chosen by

```text
mu_k(s_{k,p};xi_k) ~ p |lambda_k|,
```

then for an edge-log packet

```text
x_{k,i}=xi_k+(t_i+o(1))/lambda_k
```

the normalized rows satisfy

```text
Phi_{k,s_{k,p}}(x_{k,i}) / Phi_{k,s_{k,p}}(xi_k)
  -> exp(sigma p t_i),
```

where `sigma=sign(lambda_k)` after passing to a subsequence.  On compact
separated local coordinates this is a rectangular Vandermonde matrix.

This remains a valid local support lemma for the left-edge integer-row model
and for any orientation-safe row model whose product asymptotic supplies the
same exponential row limit.

## Why it is not the current active blocker

The current repo has already moved one layer further:

- `PO3EndpointRowProductAsymptoticCertificate` records the orientation-safe
  product asymptotic with a free slope parameter `alpha`;
- `PO3FractionalVandermondeStableProjectionCertificate` records the right-edge
  fractional Vandermonde stable-projection branch;
- `po3_endpoint_rows_stable_projection_of_fractional_right_edge_vandermonde`
  consumes bounded-separated fractional nodes and row errors;
- `po3_fractional_right_edge_capture_route_kill_of_node_collapse` records the
  collapse obstruction.

So the live blocker is now:

```text
prove the normalized shifted-remainder/mirror row errors are small
for the already selected orientation-safe/fractional endpoint rows,
or record the precise route-kill.
```

This is the same obstruction previously named in
`h1_po3_square_2d3_two_endpoint_shifted_error_2026_04_24.md` and sharpened by
`h1_po3_square_2d3_log_loss_mirror_control_2026_04_25.md`.

## Next theorem-target

Use the following active target name:

```text
PO3-square.2d3.shifted-error-after-stable-rows
```

Statement shape:

```text
Assume:
  - threshold-exhaustive packet selection;
  - endpoint-row product asymptotic for the selected rows;
  - bounded-separated stable projection, or a supplied stable-projection
    constant C_k;
  - log-loss mirror control: eta_{k,rho} log(2+xi_k) -> 0;
  - far mirror tail small;
  - omitted row-effective A-mass small by threshold exhaustion.

Then:
  epsilon_{k,rho} -> 0 for all selected rows.

Therefore:
  stable projection capture applies.
```

Failure criterion:

```text
Kill this branch if the normalized row error does not tend to zero below the
stable-projection conditioning scale, i.e. C_k ||epsilon_k|| does not tend to 0.
```

In component row-error bookkeeping, remember the loss

```text
||epsilon_k||_2 <= sqrt(r_k) max_rho |epsilon_{k,rho}|.
```

## Operational conclusion

Do not ask Proshka for another generic Vandermonde derivation.  The next
question should force the fork:

```text
Which is the faster honest theorem:
  A. prove fractional-node separation for the threshold packet;
  B. assuming stable rows, prove shifted-remainder/mirror row errors
     epsilon_{k,rho}->0?

Give exact hypotheses, proof skeleton, and route-kill.
```
