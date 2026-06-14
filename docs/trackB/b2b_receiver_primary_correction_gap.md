# Track B B2b: Receiver-Primary Correction Gap

Status: B2 theorem-shape audit.  This is not a proof of E5p, not a proof of
RH, and not a Lean proof file.

This note refines `docs/trackB/b2b_clv_receiver_primary.md`.  The previous
probe found a genuinely small Selberg-receiver residual:

```text
D_R := P(R) - P0(R),    R = M^+_{[2K,4K],delta}.
```

The question here is whether that small residual actually controls the
original hard edge defect

```text
D_I := P(1_I) - P0(1_I),    I = [2K,4K].
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

All finite probes in this note use the Step13 raw prime weights in raw `a`
coordinates.  No Q3 evenization factor is silently inserted.

## Allowed Inputs

- `UNCONDITIONAL`: Selberg--Vaaler interval receiver formulas from
  `docs/trackB/clv_pair.md`.
- `UNCONDITIONAL`: CLV Gaussian subordination / Beurling--Selberg framework.
  Source: https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL`: Guinand--Weil / Weil quadratic-form identity as a classical
  explicit-formula framework, with positivity treated only where already
  provided by Q3 finite PSD data.  Bombieri's survey/article page records the
  equivalence of Weil quadratic-form PSD and RH, so positivity is not imported
  as a free theorem input.  Source: https://eudml.org/doc/252338
- `UNCONDITIONAL / finite-dimensional linear algebra`: projected generalized
  eigenvalue diagnostics on the current packet `kerQ`.

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap conclusions.

Shape reference only:

- Carneiro--Milinovich--Soundararajan use Fourier optimization plus the
  explicit formula for prime gaps, but their prime-gap conclusion assumes RH.
  Source: https://arxiv.org/abs/1708.04122

## Local Search Synthesis

`q3_docs` searches for receiver-primary / admissible-lift / finite-Weil-model
theorem shapes returned:

- the canonical Q3 normalization `Q = arch_term - prime_term`;
- `Q*` / `w_Q(n)=2*Lambda(n)/sqrt(n)` notes;
- older route notes saying standalone prime-block PSD factorization is false
  on packet space;
- Step33 finite Weil receiver structures, where a true receiver records both
  Arch and Prime sides and proves a `weilForm = quadForm C` identity.

No local result says that a Selberg interval receiver can replace the hard
edge in E5p without paying a correction term.

## Exact Algebraic Decomposition

Let `R` be a receiver weight, for example the Selberg majorant
`M^+_{I,delta}`.  Define finite projected operators:

```text
P(W)  = prime-side packet operator with scalar weight W(a),
P0(W) = continuum / local-prime-density operator with the same weight W(a).
```

Then:

```text
D_I = P(1_I) - P0(1_I),
D_R = P(R)   - P0(R).
```

For the majorant receiver,

```text
B_R^+ := (P(R) - P(1_I)) - (P0(R) - P0(1_I)).
```

The exact identity is:

```text
D_I = D_R - B_R^+.
```

For a minorant receiver,

```text
B_R^- := (P(1_I) - P(R)) - (P0(1_I) - P0(R)),
D_I = D_R + B_R^-.
```

This identity is a D2 guardrail.  A receiver-primary proof of the original
E5p cannot stop after bounding `D_R`; it must either:

1. prove the E5p ledger may be restated with `D_R` instead of `D_I`;
2. prove `B_R^+` or `B_R^-` is controlled in the Q3 cone;
3. construct a different receiver for which the correction cancels by
   structure.

## Probe Update

`scripts/trackb_edge_operator_probe.py clvrecv` now reports:

```text
bridge_correction_plus_opnorm
bridge_correction_minus_opnorm
receiver_identity_plus_max_abs_error
receiver_identity_minus_max_abs_error
```

The reconstruction identity is numerically exact at floating precision.  For
example, at `K=3.5`, `ell=1.375`, `delta=1`:

```text
||D_R||_G                  ~= 0.00101418
||D_I||_G                  ~= 0.23848631
||B_R^+||_G                ~= 0.23863364
receiver identity error    ~= 2e-17
scalar bridge R_K           ~= 12.51649
```

So the scalar bridge is far too expensive, but the exact correction is not
small either: it is essentially the original hard-edge fluctuation.

## Stable Schedule Results

Using the stable packet widths from `docs/trackB/b2b_stability_schedule.md`:

```text
.venv/bin/python scripts/trackb_edge_operator_probe.py clvprimary \
  --K 2 2.5 3 3.5 \
  --receiver-delta 0.25 0.5 1 2 4 8 \
  --p0-na 801 --receiver-grid-nt 4001
```

At the deltas minimizing `||D_R||_G`:

```text
K=2.0:
  ell = 0.75
  best smooth delta = 0.5
  ||D_R||_G ~= 0.00516878
  ||D_I||_G ~= 0.10143342
  ||B_R^+||_G ~= 0.10196672

K=2.5:
  ell = 1.375
  best smooth delta = 1.0
  ||D_R||_G ~= 0.00197082
  ||D_I||_G ~= 0.41937898
  ||B_R^+||_G ~= 0.41939476

K=3.0:
  ell = 0.75
  best smooth delta = 0.5
  ||D_R||_G ~= 0.00660776
  ||D_I||_G ~= 0.10963611
  ||B_R^+||_G ~= 0.11346267

K=3.5:
  ell = 1.375
  best smooth delta = 1.0
  ||D_R||_G ~= 0.00101418
  ||D_I||_G ~= 0.23848631
  ||B_R^+||_G ~= 0.23863364
```

Four-point power fits:

```text
smooth receiver:
  ||D_R||_G ~= 0.01869 * K^(-1.89054)
  max_abs_log_residual ~= 1.03735

hard edge:
  ||D_I||_G ~= 0.08830 * K^(0.73388)
  max_abs_log_residual ~= 0.88560

bridge correction:
  ||B_R^+||_G ~= 0.08802 * K^(0.74719)
  max_abs_log_residual ~= 0.87657
```

The correction tracks the hard edge, not the small receiver residual.

## B2b Theorem Shapes

### RP1: Pure Receiver Replacement

Claim shape:

```text
E5p ledger can be restated with D_R in place of D_I.
```

This would make the small CLV residual relevant immediately.

Failure mode:
It may prove a smoothed E5-like statement rather than the original edge
defect.  This is a route-equivalence theorem, not a numerical estimate.

### RP2: Correction Kill

Claim shape:

```text
||B_R^+||_G <= C * K^(-c)
```

for the Q3 boundary-null cross-correlation cone.

Current evidence:
False-looking for the current Step13 B-spline packet family.  The measured
`B_R^+` has the same scale as `D_I` and no positive B3 decay signal.

### RP3: One-Sided PSD Absorption

Claim shape:

```text
B_R^+ has the sign needed to be absorbed by zero-side PSD.
```

Current evidence:
The projected bridge and continuum bridge matrices are indefinite; standalone
prime-block PSD was already rejected locally.  This shape needs a new
structured cone theorem, not scalar Selberg majorization.

### RP4: Structured Receiver

Claim shape:

```text
Find R = R_K,cone so that D_R is small and B_R^+ cancels structurally.
```

This is the remaining constructive door.  It is no longer the ordinary
Selberg interval pair alone; it would be a CLV/Selberg receiver corrected by
the Q3 Hermitian-square cone or by a finite-Weil-model constraint.

## Verdict

`GAP(receiver-primary correction theorem missing)`.

The ordinary Selberg receiver successfully creates a small smoothed residual
`D_R`, but it does not by itself control the original E5p hard edge.  The exact
identity shows that the missing object is the bridge correction `B_R`, and the
current finite evidence says `B_R` is essentially the hard-edge obstruction
again.

Therefore the next Track B move should not be another scalar bandwidth sweep.
It should be one of:

1. prove RP1: the E5p ledger genuinely accepts the receiver-primary smoothed
   test object;
2. design RP4: a cone-adapted receiver whose correction term cancels;
3. escalate this exact correction identity to Proshka for theorem-shape
   review.

## Proshka Audit Block

Claim:
The Selberg receiver residual `D_R = P(M^+) - P0(M^+)` is small, but the exact
identity for the original hard edge is

```text
D_I = D_R - B_R^+,
B_R^+ = (P(M^+) - P(1_I)) - (P0(M^+) - P0(1_I)).
```

Point of blockage:
`B_R^+` is not a small error in the current packet family.  At K=3.5 it has
`G`-opnorm about `0.23863`, while the hard edge has about `0.23849` and the
receiver residual has about `0.00101`.

What was tried:
- Added bridge-correction diagnostics to `clvrecv`.
- Verified the exact receiver decomposition numerically to floating precision.
- Ran the stable packet schedule over K=2,2.5,3,3.5 and
  `delta in {0.25,0.5,1,2,4,8}`.
- Confirmed that the correction tracks the hard edge, not the smoothed
  receiver residual.
- Ran local `q3_docs` search for admissible-lift / finite-Weil receiver shapes.
- Ran primary-source search around CLV, Fourier optimization, and Weil's
  quadratic functional.

Minimal example:
At K=3.5, `ell=1.375`, `delta=1`:

```text
||D_R||_G ~= 0.001014
||D_I||_G ~= 0.238486
||B_R^+||_G ~= 0.238634
identity error ~= 2e-17
```

Question for Proshka:
Can E5p be reformulated so that the CLV/Selberg receiver residual `D_R` is the
actual ledger object, or must we construct a cone-adapted receiver that kills
`B_R^+`?  If the latter, what structural condition should replace scalar
`M^+ >= 1_I`?

## Follow-Up

`docs/trackB/b2b_affine_receiver_no_free_lunch.md` tests the simplest
cone-adapted repair:

```text
R_theta = 1_I + theta * (M^+ - 1_I).
```

The result is a route-kill for affine Selberg interpolation with separate
residual/correction bounds.  Since

```text
D_I = D_theta - B_theta,
```

the separate-bound cost `||D_theta||_G + ||B_theta||_G` is bounded below by
`||D_I||_G`; the finite scan attains its best total at `theta=0`, i.e. no
receiver smoothing.  The remaining doors are route-equivalence for the
smoothed receiver ledger, a nonlinear/cone-adapted structural cancellation of
`B_R`, or a return to direct finite-op / ordinary-prime mean control.
