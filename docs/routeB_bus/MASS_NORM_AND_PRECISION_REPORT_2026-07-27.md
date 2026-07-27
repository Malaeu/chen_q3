# MASS+NORM and centered-density precision report

## 1. Centered-density precision check

The coefficient rows were constructed in binary64 and held fixed.  Only the
finite Fourier summation at the selected grid points was recomputed with
`mpmath`, `mp.dps = 50`.

| `(m,N)` | worst aligned float64 | worst aligned mp50 | max `|mp50-float64|` over worst 20 | all worst 20 negative |
|---|---:|---:|---:|---:|
| `(53,120)` | `-3.88196915664e-9` | `-3.881969245783603364800944369152796273349227007293596e-9` | `4.222083757804877494898177454157381109195322878564704e-16` | yes |
| `(257,120)` | `-1.51362074517e-8` | `-1.513620731094502528775076032002977293872542133786594e-8` | `3.656413378666914811806707925296338968142798034325e-16` | yes |

The fixed-row violations remain under 50-digit summation.  Their absolute
scale grows from `3.88196924578e-9` to `1.51362073109e-8`, a factor
`3.89910541599`; the two-point power fit is `m^0.861895609931`.
This excludes binary64 Fourier-summation cancellation as their source, but
does not certify the exact-sign behavior of the underlying exact coefficient
construction.

## 2. Unprojected MASS+NORM probe

Float64/complex128, `N=120`, every integer `m=13,...,257`, and the same
`L²(du/u)` norm as the `kTrial` normalization.

| `m` | `Re M_m` | `|M_m|` | `||gTrial_m||` | `||P gTrial_m||` | `|M_m|/||P gTrial_m||` |
|---:|---:|---:|---:|---:|---:|
| 13 | -0.405890786544 | 0.405890786544 | 0.469347514782 | 0.469347514782 | 0.864797988187 |
| 53 | -0.410265222660 | 0.410265222660 | 0.468482812767 | 0.468482812767 | 0.875731641546 |
| 120 | -0.411037899299 | 0.411037899299 | 0.468344245647 | 0.468344245647 | 0.877640545644 |
| 257 | -0.411361991030 | 0.411361991030 | 0.468287319315 | 0.468287319315 | 0.878439312925 |

Power fits over all 245 cells:

| quantity | fit exponent `beta` in `C m^beta` | endpoint ratio `257/13` | range |
|---|---:|---:|---:|
| `|M_m|` | `+0.0029206277653` | `1.01347949909` | `[0.405890786544, 0.411361991030]` |
| `||gTrial_m||` | `-0.000473803945206` | `0.997741129049` | `[0.468287319315, 0.469347514782]` |
| `|M_m|/||P gTrial_m||` | `+0.00339443171056` | `1.01577400147` | `[0.864797988187, 0.878439312925]` |

Checks: `M_m < 0` for all 245 cells; `Im M_m = 0`; maximum projection
contraction ratio is `1.0`.  The registered plateau prediction and the
`|F⁺(0)| ≈ 0.865–0.878` control are reproduced.

