# Branch export review — operator difference to Step 32F closure

Source:

- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/docs/2026-5-5 8-39-57-________Branch_______________________.md`

Status:

- reviewed extraction from a raw branch/chat export;
- do not commit or index the raw export as-is;
- use this note as the small project-memory artifact.

## Surviving core

The branch export starts from the operator intuition

```text
Arch part - Prime part >= 0
```

and correctly sharpens it into a quadratic-form target:

```text
Hermitian square
=> zero-side positivity/negativity test
=> Weil/Arch-Prime form
=> finite Gram/kernel certificates
```

The useful part is not a new RH theorem.  It is the proof-engineering map:
operator differences must enter through endpoint-safe Hermitian-square tests
and matrix/Gram certificates, not through pointwise comparison of Arch and
Prime symbols.

## Methodology import

The Tang/Williams discussion is useful only as methodology:

- Tang-style lesson: separate search access from proof access.  Numerical
  sketches may find candidates, but the mainline needs exact or interval
  certificate inputs.
- Williams-style lesson: decompose large arguments into a proof DAG of small
  reusable blocks.  This supports the current Step 32F split into recurrence,
  finite-sum algebra, positivity, and autocorrelation assembly.

This does not import any external theorem about zeta or B-splines.

## Live Q3 consequence

The export confirms the current decision:

```text
do not open Step 33 yet
```

Step 32F is still live until the concrete centered-cardinal B-spline identities
feed the existing `BSplineTranslatedAnalyticContract` route.

The active proof chain is:

```text
centeredCardinalBSpline_succ_eq_conv_box
=> CenteredCardinalBSplineMatchesConvPower k
=> endpoint-safe AE route
=> convPower self-convolution B_k * B_k = B_(2k+1)
=> 0 < bsplineAutocorrNorm k
=> CenteredBSplineAutocorrelationClosedForm k
```

Lean already has the assembly layer:

```lean
CenteredCardinalBSplineMatchesConvPower_all_of_succ_eq_conv_box
CenteredBSplineAutocorrelationClosedForm_all_of_convPower_inputs
CenteredBSplineAutocorrelationClosedForm_all_of_recurrence_package
```

So the branch export does not require a new receiver.  It supports the current
recurrence-first closure.

## Exact next proof target

The next Lean target remains the recurrence:

```lean
centeredCardinalBSpline (k + 1)
  =
realConvolution (centeredCardinalBSpline k) centeredBoxSpline
```

The intended proof should be split into two local bricks:

1. positive-part interval integral

```lean
positivePartPower_interval_integral_centered
```

mathematically:

```text
∫_{-1/2}^{1/2} (x - y + A)_+^k dy
= ((x + A + 1/2)_+^(k+1) - (x + A - 1/2)_+^(k+1)) / (k+1)
```

2. Pascal telescope

```lean
centeredCardinalBSpline_pascal_telescope
```

mathematically:

```text
sum_j (-1)^j choose(k+1,j) (T_j - T_(j+1))
= sum_j (-1)^j choose(k+2,j) T_j
```

After those two bricks, `centeredCardinalBSpline_succ_eq_conv_box` should
become a controlled assembly proof rather than a giant mixed integral/sum
proof.

## Rejected / weakened

- Do not treat `Q = T^*T >= 0` as an RH proof.  It is automatically positive
  for any `T`; the content must be in the kernel/equivalence or in the Weil
  negative-direction contradiction.
- Do not promote the full raw branch export into source-of-truth docs.
- Do not jump to Step 33 before the autocorrelation, transform, and boundary
  scale facts are wired into the B-spline packet.

## Next action

Work in:

```text
Q3/Proofs/PSD_CenteredCardinalBSpline.lean
```

Start with the smallest local theorem that Lean can actually close:

```lean
centeredCardinalBSpline_pascal_telescope
```

or, if the integral route is already clearer in the local API,

```lean
positivePartPower_interval_integral_centered
```

Keep the raw export untracked unless the user explicitly asks to archive it.
