# Track B B2b/B3: CLV Receiver-Primary Schedule

Status: B2/B3 diagnostic.  This is not a proof certificate and does not close
E5p.  It tests the viable branch left after
`docs/trackB/b2b_clv_bridge_budget.md`:

```text
do not use M^+ as a post-hoc scalar majorant of the hard edge;
instead, make the Selberg receiver the primary explicit-formula /
Hermitian-square test object.
```

The numerical question is:

```text
If receiver-primary is a valid B2b formulation,
does ||P(M^+) - P0(M^+)||_G show B3-sized decay?
```

The theorem question is separate:

```text
Can original E5p be reformulated so that this receiver-primary object
actually controls the edge defect without a separate
P(edge) <= P(M^+) + R_K G bridge?
```

## D2 Normalization

Raw variable:

```text
a = r * log p,
I_K = [2K, 4K].
```

Q3 variable:

```text
xi = a/(2*pi),
w_Q(n) = 2*Lambda(n)/sqrt(n).
```

The Selberg receiver is applied in raw `a` coordinates.  The reported finite
operators still use the Step13 raw prime weights; no extra Q3 evenization
factor is inserted.

## Allowed Inputs

- `UNCONDITIONAL`: Selberg--Vaaler interval receivers from
  `docs/trackB/clv_pair.md`.
- `UNCONDITIONAL`: CLV Gaussian subordination / Beurling--Selberg framework.
  Source: https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL / finite-dimensional linear algebra`: fixed projected packet
  eigenvalue diagnostics on `kerQ`.

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap conclusions.

## Local And External Search Synthesis

Local `q3_docs` search for

```text
Hermitian-square explicit-formula Selberg receiver primary M+ edge defect
receiver primary explicit formula cross-correlation cone prime edge
Guinand Weil explicit formula test function Selberg majorant zero-side PSD
```

returned the corrected cone, existing `Q^star` / Weil functional packaging,
prime-term bridge files, and old explicit-formula decomposition notes.  It did
not return a theorem that makes the Selberg receiver the primary
Hermitian-square object for E5p.

External primary-source scan confirms the genre:

- Carneiro--Milinovich--Soundararajan use Fourier optimization plus explicit
  formula for prime-gap problems, but their prime-gap conclusion assumes RH.
  Source: https://arxiv.org/abs/1708.04122
- Carneiro--Chirre--Milinovich use bandlimited majorants in zeta estimates,
  again with RH assumptions in the stated zeta bounds.
  Source: https://arxiv.org/abs/1710.10362
- CLV supplies unconditional extremal-function technology, not the missing Q3
  cone formulation by itself.
  Source: https://arxiv.org/abs/1008.4969

Therefore the allowed input remains only the unconditional receiver
construction and finite-dimensional diagnostics.  The missing theorem is
internal to our Q3 cone/explicit-formula formulation.

## Probe Mode

Implementation:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py clvprimary \
  --K 2 2.5 3 3.5 \
  --receiver-delta 0.25 0.5 1 2 4 8 \
  --p0-na 801 --receiver-grid-nt 4001
```

The new `clvprimary` mode wraps `clvrecv`, uses the stability-filtered packet
widths from `docs/trackB/b2b_stability_schedule.md`, and reports:

```text
best_smooth_epsilon
  = min_delta ||P(M^+) - P0(M^+)||_G,

bridge_R_at_best_smooth
  = max(0, -lambda_min_G(P(M^+) - P(edge)))
    at the same delta,

best_total_upper_budget
  = min_delta (bridge_R_plus + smooth_epsilon).
```

Only `best_smooth_epsilon` is relevant to the receiver-primary hypothesis.
`best_total_upper_budget` is the already-failing scalar bridge diagnostic.

## Stable Schedule Results

```text
K=2.0:
  ell = 0.75
  best smooth delta = 0.5
  best smooth epsilon ~= 0.00516878
  bridge R at best smooth ~= 3.52106
  hard edge epsilon ~= 0.101433

K=2.5:
  ell = 1.375
  best smooth delta = 1.0
  best smooth epsilon ~= 0.00197082
  bridge R at best smooth ~= 3.47725
  hard edge epsilon ~= 0.419379

K=3.0:
  ell = 0.75
  best smooth delta = 0.5
  best smooth epsilon ~= 0.00660776
  bridge R at best smooth ~= 10.99006
  hard edge epsilon ~= 0.109636

K=3.5:
  ell = 1.375
  best smooth delta = 1.0
  best smooth epsilon ~= 0.00101418
  bridge R at best smooth ~= 12.51649
  hard edge epsilon ~= 0.238486
```

The receiver-primary smooth fit over these four points is:

```text
best_smooth_epsilon(K) ~= C*K^(-c),
C ~= 0.01869,
c ~= 1.89054,
max_abs_log_residual ~= 1.03735.
```

The exponent is positive, but the residual is large and the four-point sample
is visibly non-monotone:

```text
0.00517, 0.00197, 0.00661, 0.00101.
```

So this is not a theorem-scale B3 certificate.  It is a strong numerical
signal that the receiver-primary object is much better behaved than the hard
edge, and a weak/early signal for possible B3 decay.

## Interpretation

The receiver-primary route has the opposite profile from the scalar bridge:

```text
P(M^+) - P0(M^+)
```

is small on the tested stable packet schedule.

But the bridge penalty at the same best smooth deltas is huge:

```text
K=2:   R ~= 3.52
K=2.5: R ~= 3.48
K=3:   R ~= 10.99
K=3.5: R ~= 12.52
```

Therefore this route cannot be interpreted as a hard-edge majorization.  It is
only meaningful if B2b can be reformulated so that the Selberg receiver is the
actual explicit-formula/Hermitian-square test object from the start.

## Verdict

`PARTIAL(receiver-primary CLV residual is small)`.

`GAP(receiver-primary formulation theorem missing)`.

The next mathematical target is not another scalar majorant.  It is the
formulation theorem:

```text
Original E5p edge defect
  -> receiver-primary Guinand-Weil / Hermitian-square test object
  -> zero-side PSD controls the receiver term
  -> prime-side residual is the measured P(M^+) - P0(M^+).
```

If this formulation cannot be made precise, then the current CLV receiver
evidence remains only a useful diagnostic, not a route to E5p.

## Proshka Audit Block

Claim:
The Selberg receiver-primary object has small measured prime-continuum
residual on the stable packet schedule.  Over K=2,2.5,3,3.5 the best smoothed
residuals are roughly `0.00517, 0.00197, 0.00661, 0.00101`.

Point of blockage:
This does not bound the hard edge unless we can formulate E5p with the
receiver as the primary Hermitian-square explicit-formula test object.  The
post-hoc scalar bridge is already fatal because it pays a large `R_K`.

What was tried:
- Added `clvprimary` schedule mode.
- Ran stable packet schedule over K=2,2.5,3,3.5 and
  `delta in {0.25,0.5,1,2,4,8}`.
- Compared best smooth residuals to hard-edge epsilons and bridge penalties.
- Ran local `q3_docs` search for receiver-primary / Hermitian-square theorem
  shapes.
- Ran short primary-source search around Fourier optimization and
  bandlimited explicit-formula methods.

Minimal example:
At K=3.5, `ell=1.375`, `delta=1`:

```text
best smooth epsilon ~= 0.001014
hard-edge epsilon ~= 0.238486
bridge R at best smooth ~= 12.51649
```

Question for Proshka:
Can E5p be restated so that the Selberg receiver is the primary
Guinand-Weil/Hermitian-square test object, avoiding hard-edge majorization?
If yes, what is the exact Q3 cone statement and where does zero-side PSD enter?

## Follow-Up

`docs/trackB/b2b_receiver_primary_correction_gap.md` refines this blocker by
writing the exact identity

```text
D_I = D_R - B_R^+,
B_R^+ = (P(M^+) - P(1_I)) - (P0(M^+) - P0(1_I)).
```

The follow-up probe shows that `B_R^+` tracks the hard-edge defect on the
tested stable packet schedule.  Therefore the missing theorem is not just
"make the receiver primary"; it is either a route-equivalence theorem that
changes the E5p ledger to the receiver object, or a cone-adapted receiver that
cancels `B_R^+`.
