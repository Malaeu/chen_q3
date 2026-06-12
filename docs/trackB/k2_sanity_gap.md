# Track B B1 K=2 Sanity Gate

Status: GAP(measured CLV-through-cone comparison missing).

This note records the B1 sanity-gate state after extracting the Selberg/CLV
edge-strip pair in `docs/trackB/clv_pair.md`.

## Gate Requirement

For `K = 2`, compare:

1. a numerical CLV estimate for the edge strip `[2K, 4K] = [4, 8]`;
2. a measured Q3 cross-correlation edge defect on the live cone;
3. the inequality direction: the CLV estimate must majorize the measured
   defect, otherwise the formula normalization or cone transport is wrong.

This is a gate, not a theorem. No RH claim follows from this note.

## D2 Normalization

Raw-log variable:

```text
a = r * log p
I_K = [2K, 4K]
K = 2 -> I_K = [4, 8]
prime weight = log(p) / p^(r/2)
```

Q3 formal `xi` variable:

```text
xi_n = log n / (2*pi)
even prime term weight = 2 * Lambda(n) / sqrt(n)
```

Therefore the raw-log edge `[4, 8]` corresponds to
`xi in [2/pi, 4/pi]`. Any later Lean or paper statement must explicitly state
which variable is being used.

## Local Search Result

No saved proof-grade artifact was found that directly records:

```text
K=2 edge-strip CLV estimate >= measured live-cone CC defect
```

The nearest existing numerical instrument is:

```text
q3.lean.aristotle/scripts/q3_psdpd_step13_pilot.py
```

That script is a reconnaissance pilot. It builds the finite B-spline packet
matrices `G, A, P, P0, Pnu, Q, N` and checks the split
`C = A - P = (A - P0) - (P - P0)`. It is not an interval-certified proof.

## Step13 Pilot Run

Command:

```bash
.venv/bin/python q3.lean.aristotle/scripts/q3_psdpd_step13_pilot.py \
  --L 4 --ell 0.35 --delta 0.5 --k-spline 5 \
  --arch-tmax 120 --arch-nt 8001 --p0-na 8001
```

Key output:

```text
prime_power_shifts=465
W_L=sum_weights=1.0677377388948221e+02
dim ker(Q)=14
||Q N||_F=5.180e-15
||C - (R-Pnu)||_F=6.280e-16
eig(Cc, Gc), C=A-P: min=-4.7426525730716631e-07, max=1.1645179835318038e+00
eig(Rc=A-P0): min=-4.5356334897461975e-01, max=1.2435881921980667e-01
||Pnu||_F=2.3412260105337612e+00
```

Interpretation:

- The algebraic split is numerically consistent at Frobenius error `6.28e-16`.
- The pilot covers all shifts `a <= 2L = 8`, not only the edge `[4, 8]`.
- `Rc = A - P0` is not positive definite in this coarse pilot, so the relative
  `eig(Pnu, R)` certificate is unavailable here.

## Edge-Only Extraction

Using the same Step13 formulas without modifying the script, shifts were
filtered to:

```text
4 <= r * log(p) <= 8
```

and the continuous model `P0_edge` was integrated over `[4, 8]`.

Result:

```text
K=2 raw-log edge [4,8] via Step13 pilot params
n_centers 16
dim_kerQ 14
edge_prime_power_shifts 441
total_shifts 465
edge_weight_sum 9.4582127971904143e+01
P0_edge_mass_model_integral 9.4418187868427168e+01
||P_edge||_F 4.3071259357080670e+01
||P0_edge||_F 4.2938375520338312e+01
||Pnu_edge||_F 1.0032536233719529e+00
||Pnu_edge^circ||_F 8.3570919987750070e-01
eig(Pnu_edge^circ,Gc): min=-4.4167187609865910e-01, max=4.3707976289804534e-01
opnorm_G(Pnu_edge^circ) 4.4167187609865910e-01
```

Interpretation:

- This is the current nearest measured edge defect proxy.
- It is not yet the B1 sanity certificate because it has not been majorized by
  a CLV-through-cone bound.
- It is useful as a target number: the first useful CLV cone bound should beat
  `0.442` in the same projected `G`-operator normalization, or explain why that
  normalization is not the one used by the theorem.

## CLV Formula Sanity

For the Selberg interval pair in `docs/trackB/clv_pair.md`, with raw-log
interval `[4, 8]` and `delta = 1`:

```text
int M^- = 3
int chi_[4,8] = 4
int M^+ = 5
one-sided L1 error = 1
Fourier support in [-1, 1]
exponential type <= 2*pi
```

This confirms the scalar interval constants, not the cone estimate.

## Why B1 Is Not Fully Closed

The missing object is a theorem-shaped inequality of the form:

```text
measured_edge_defect_on_C_K <= epsilon_K^CLV
```

with:

- the same `G` or energy normalization as the Q3 cone;
- exact raw-log versus `xi` scaling;
- no split into non-bandlimited `g_+` and `g_-`;
- every analytic input marked `UNCONDITIONAL`.

Until that inequality is written and checked numerically for `K=2`, the B1
sanity gate remains open.

## B2 Route Decision

Proceed with B2b first.

Reason:

- B2a risks losing the bandlimited cross-correlation cone when replacing
  `g` by positive and negative parts.
- B2b keeps the Hermitian square / explicit-formula structure and attempts to
  place the Selberg majorant/minorant on the explicit-formula test function
  itself.
- The intended replacement for the RH-conditional zero-side positivity in
  prime-gap arguments is the already local PSD structure of the Q3 cone.

## Proshka Blocker Draft

Claim:
Selberg/CLV gives an unconditional interval majorant/minorant for the raw-log
edge strip `[4, 8]`, but this alone does not bound the Q3 edge defect unless it
is transported through the bandlimited Hermitian-square cone.

Point of blockage:
The naive B2a split `g = g_+ - g_-` drops bandlimitation and is invalid. The
candidate B2b route must apply the explicit formula to the whole
Hermitian-square test function, then use Q3 zero-side PSD to replace the
RH-conditional positivity used in prime-gap applications.

What was tried:
- Extracted the Selberg pair and constants.
- Verified scalar interval constants for `K=2`, `delta=1`.
- Ran the Step13 pilot at `L=4`.
- Extracted an edge-only projected defect proxy:
  `opnorm_G(Pnu_edge^circ) = 4.4167187609865910e-01`.

Minimal example:
Use raw-log edge `[4,8]`, packet parameters
`L=4, ell=0.35, delta=0.5, k_spline=5`, and boundary-null projection `N` from
`Q = (exp(u/2), exp(-u/2))`. Show or refute an unconditional inequality that
majorizes `N^T(P_edge - P0_edge)N` by an explicit Selberg/CLV bound in the same
`G` normalization without passing through non-bandlimited positive parts.
