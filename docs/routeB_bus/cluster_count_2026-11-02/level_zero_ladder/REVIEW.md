# Bounded final review: level–zero ladder

Independent read-only review of `matching.py`, `roots.py`, `root_method.md`,
`RESULT.md`, and supporting serialization/eigenpair code. No full numerical
rerun, source-matrix recomputation, or Git operation was performed.

## Mathematical definitions and normalization

**CONFIRMED.** The basis is the unit physical cosine basis
`φ_n=d_n(−1)^n cos(2πnx/L)/√L`, zero-extended from `[-L/2,L/2]`.
The direct sinc transform and its derivative in `roots.py` have the correct
factor `L/2`, the modal alternating sign, and `d_n` through `c_n=d_n V_ni`.
Away from removable modal values the resulting expression is

`F_i(t)=2t sin(tL/2)/√L Σ_n d_n V_ni/(t²−(2πn/L)²)`.

Writing `Ω_m=2πm/L`, its numerator in `y=(t/Ω_m)²` is, up to a common nonzero
factor, `Σ_n c_n Π_(k≠n)(y−k²/m²)`. The rounded-rational polynomial is used
only for seed isolation, then checked on the full-precision direct transform.
Exact isolation applies to the rounded polynomial; the report correctly does
not promote it to an enclosure of an exact CCM eigenvector's roots.

The modal roots `2πk/L`, k>m, are genuinely common structural zeros of every
carrier vector. They are separately flagged. Interior modal values are
removable and are not treated as automatic roots. Negative/nonreal y roots
are counted separately; excited vectors are not assumed real-rooted.

## Matching definitions

**CONFIRMED.** Primary B=2 means positive eigenvalues at least m^(−2), sorted
in ascending order, paired ordinally with the first equally many positive
zeta ordinates. B=4/8 are separately labeled sensitivity choices.
This is an explicit diagnostic convention, not a theorem-derived map.

The cost matrix takes each vector's nearest retained positive real Fourier
root and divides its distance from γ_j by the smaller adjacent zeta gap
(the first ordinate uses the next gap). Hungarian assignment is a bijection
between levels and these ordinates; independent minimization permits repeated
levels. The code and report agree on these distinct optimization problems.
Structural-root ties can choose a level arbitrarily, as the report states.

The collapse coordinate is `x=γ_j/Ω_m`, not an eigenvector's own root divided
by Ω_m. The curves interpolate `log λ` on their common x interval without
extrapolation. The reported factors are `exp(max_m logλ−min_m logλ)` there.
Their interpretation depends on the declared ordinal assignment and threshold.

## Reporting and interpretation

No material mathematical/reporting error found in the bounded review.
The B=2 median factor1.5299 and maximum factor10.5189 permit a rough upper-
branch similarity but do not show a tight threshold-independent collapse.
The report preserves that distinction and reports larger B=4/8 spreads.
It does not incorrectly infer nonexistence of an arbitrary F(x,m) or an
asymptotic law from four carriers.

The ordinal matching distances and the optimized reordering/many-to-one
outcomes justify the scoped statement that this finite experiment does not
support one distinct lifted Weil energy level per zeta ordinate.
That is not a refutation of ground-transform zero tracking, CCM's perturbed
scaling-operator theorem, the broader counting route, RH, or NOESCAPE.
The report correctly distinguishes the two spectra and changes no theorem status.

Internal transform residuals are distinguished from residuals at the saved
125-digit root locations. `|F/F′|` is labeled a first-order position residual,
not an interval radius. Repeating the m40 check with a second precision/
quadrature source is a stability check, not a separate analytic method or
an interval certificate.

## Bounded consistency checks performed

Read the existing CSV/JSON metadata, without rerunning root extraction:
4018 rows,67 profiles,528 assignment rows. B=2 lifted counts are7,11,15,19;
Hungarian ordinal agreements are1,0,2,1; independent matching uses4,2,2,3
distinct levels. The stored maximum serialized position residual is
`4.97824346791e−123`, consistent with the report's rounding.
Off-lattice roots in the retained files are separated from all interior modal
lattice points, so no interior-pole cancellation is mislabeled in these data.

Minor documentation findings were sent to root: the structural lattice loop
keeps the next **two** points beyond120; replay of the serialization diagnostics
requires `root_serialized.py`. Root corrected both. Root also added explicit
definitions of Ω_m, x, and natural logarithms to the report/method notation.

Reviewed numerical code SHA256:

- `matching.py`: `9a9983b1e0d651fbb73d03ea19ccb57af1ab04d05642cfe7906689e0b6030ece`
- `roots.py`: `3eb32fa81478033eb730f127a9dfb6d274f6c1045dcf9d414ed0d9b9bc6f6a5b`

Verdict: **PASS for the stated finite diagnostic scope**. No cofinal or exact-
arithmetic certification is supplied by this review.
