# Q3 PSD-pd Step 13 Numerical Pilot (2026-05-03)

Status: in progress / reconnaissance

Placement:

- This is a finite numerical pilot for the fallback `PSD-pd` certificate route.
- It does not claim RH.
- It is not proof-grade; `A` and `P0` are currently computed by floating
  trapezoid quadrature.

Script:

```text
scripts/q3_psdpd_step13_pilot.py
```

## Built objects

The pilot builds:

```math
G,\quad A,\quad P,\quad P_0,\quad P_\nu=P-P_0,\quad Q,\quad N.
```

It checks:

```math
C^\circ=N^\ast(A-P)N,
\qquad
\lambda_{\min}(C^\circ,G^\circ),
```

and also tries the relative fluctuation certificate:

```math
R^\circ=N^\ast(A-P_0)N,
\qquad
\lambda_{\max}(P_\nu^\circ,R^\circ).
```

Notation:

- `k_spline`: B-spline degree;
- `r_pow`: prime-power exponent in `p^r_pow`.

## Baseline run

Command:

```text
uv run python q3.lean.aristotle/scripts/q3_psdpd_step13_pilot.py \
  --L 3.0 \
  --ell 0.35 \
  --delta 0.25 \
  --k-spline 5 \
  --arch-tmax 180 \
  --arch-nt 24001 \
  --p0-na 12001
```

Output summary:

```text
n_centers=22
prime_power_shifts=98
dim ker(Q)=20
||Q N||_F=1.750e-15
||C - (R-Pnu)||_F=1.811e-15
eig(Gc): min=7.9489735788481686e-01, max=1.1937183662624231e+00
eig(-P0c, Gc): min=6.4214533486977570e-03, max=8.0803225388637134e-01
eig(Cc, Gc), C=A-P: min=1.0104409960557877e-08, max=2.1627752487255916e+00
eig(Rc=A-P0): min=-1.2860682916019393e+00, max=5.5162105498780323e-01
```

Verdict:

- boundary projection is numerically clean;
- the split identity `C=R-Pnu` is numerically clean;
- `-P0` passes the Step 9 sanity check with a real gap;
- direct finite `C=A-P` is positive but with a tiny gap near `1e-8`;
- `R=A-P0` is not positive definite on this finite level, so the simple
  relative certificate `lambda_max(Pnu,R)<=1` is unavailable as stated.

## Quadrature stability check

Command:

```text
uv run python q3.lean.aristotle/scripts/q3_psdpd_step13_pilot.py \
  --L 3.0 \
  --ell 0.35 \
  --delta 0.25 \
  --k-spline 5 \
  --arch-tmax 260 \
  --arch-nt 48001 \
  --p0-na 24001
```

Output summary:

```text
eig(-P0c, Gc): min=6.4214377234407894e-03, max=8.0803223826322035e-01
eig(Cc, Gc), C=A-P: min=1.0106683705041208e-08, max=2.1627752487287157e+00
eig(Rc=A-P0): min=-1.2860683102394381e+00, max=5.5162104256978162e-01
```

Verdict:

- the tiny direct gap is stable under a stronger quadrature setting;
- the negative `R` direction is not a coarse quadrature artifact.

## Quick sweep

Sweep:

```text
k_spline in {3,5,7,9}
ell in {0.30,0.35,0.45,0.60}
L=3.0, delta=0.25, arch_tmax=180, arch_nt=24001, p0_na=12001
```

Observed direct generalized gaps:

| `k_spline` | `ell` | min eig `C^circ,G^circ` |
| --- | ---: | ---: |
| 3 | 0.30 | `6.0284860435723095e-07` |
| 3 | 0.35 | `9.7341637944792784e-07` |
| 3 | 0.45 | `1.2660610506572113e-07` |
| 3 | 0.60 | `1.0225515021772278e-08` |
| 5 | 0.30 | `1.8257128076910202e-08` |
| 5 | 0.35 | `1.0104409960557877e-08` |
| 5 | 0.45 | `1.0601108115805580e-09` |
| 5 | 0.60 | `1.3010838582712450e-11` |
| 7 | 0.30 | `3.3993674799520438e-07` |
| 7 | 0.35 | `-4.7601813401060654e-09` |
| 7 | 0.45 | `-6.3519840924594830e-09` |
| 7 | 0.60 | `-3.2709092374594307e-08` |
| 9 | 0.30 | `1.9647793450521012e-05` |
| 9 | 0.35 | `1.0855948303028751e-07` |
| 9 | 0.45 | `-8.2932560632251687e-07` |
| 9 | 0.60 | `-4.0199862165420185e-06` |

`-P0` stayed positive in all sweep cases, with minimum generalized eigenvalue
near `6.3e-3`.

`R=A-P0` stayed indefinite in all sweep cases, so the relative certificate
with base `R` is not currently the right finite pilot check without a quotient
or a modified positive base.

## Interpretation

The good news:

- Step 9 Green negativity sanity is numerically robust.
- Direct boundary-null `C=A-P` is extremely close to PSD and often positive.
- The B-spline engine is useful enough to expose the actual frontier.

The warning:

- the direct gap is often microscopic;
- some smoother/wider choices cross slightly negative;
- this is not yet a stable proof-grade certificate.

The main mathematical signal:

```math
\boxed{
P_0\ \text{is handled. The remaining issue is a near-kernel of }A-P.
}
```

The next pilot should extract the worst generalized eigenvector for the
near-zero direction and classify it:

- boundary artifact;
- Arch low-frequency mode;
- spline-smoothness artifact;
- genuine dense-limit obstruction.

## Implementation notes

The script uses:

- `scipy.linalg.eigh` for symmetric generalized eigenvalue checks;
- `scipy.linalg.null_space` for the boundary-null basis;
- `scipy.special.digamma` for the Archimedean multiplier;
- `numpy.sinc(x/pi)` for the unnormalized sinc `sin(x)/x`.

References:

- SciPy `eigh`:
  `https://docs.scipy.org/doc/scipy/reference/generated/scipy.linalg.eigh.html`
- SciPy linear algebra / `null_space`:
  `https://docs.scipy.org/doc/scipy/reference/linalg.html`
- SciPy special functions / `digamma`:
  `https://scipy.github.io/devdocs/reference/generated/scipy.special.digamma.html`
- NumPy `sinc`:
  `https://numpy.org/doc/stable/reference/generated/numpy.sinc.html`

## Next target

Step 14 should add diagnostics:

- save or print the worst generalized eigenvector;
- compute its coefficient profile in `u`;
- compute its spectral profile `|H(it)|^2`;
- decompose its energy into `A`, `P`, `P0`, `Pnu`;
- run a local refinement around the best positive cases, especially
  `(k_spline,ell)=(9,0.30)`, `(3,0.35)`, and `(7,0.30)`.
