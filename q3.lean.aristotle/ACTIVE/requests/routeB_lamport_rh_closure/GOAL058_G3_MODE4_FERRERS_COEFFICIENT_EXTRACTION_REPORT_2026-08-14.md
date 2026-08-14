# Goal 058 G3 mode-four Ferrers coefficient-extraction report

Date: 2026-08-14

Lane: `CHALLENGER / NOT_RH`

Execution base:

```text
HEAD = origin/rh_clean = 7b4d1b02
P9_STRICT_PASS
Route B CHECK: OK
```

The Lean file and this report were kept uncommitted and unpushed through the
bounded execution and validation phase pending review in the living Goal 058
Proshka chat.

## Result

```text
G3_MODE4_FERRERS_FUNCTION_NONZERO_FROM_COEFFICIENT_EXTRACTION_PROVED
```

Owned Lean file:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0Mode4FerrersCoefficientExtraction.lean
```

Direct import:

```text
Q3.Proofs.RouteB.D0Mode4FerrersRegularEvenProlateSolution
```

## Public surface

The new public heads are:

```text
Q3.RouteB.mode4OrdinaryLegendre_intervalIntegral_eq_zero_of_pos
Q3.RouteB.mode4FerrersSeries_intervalIntegral_eq_two_mul_coefficient_zero
Q3.RouteB.mode4FerrersSeries_ne_zero_of_coefficient_zero_ne_zero
Q3.RouteB.Mode4FerrersRegularEvenProlateSolution.ferrersSeries_ne_zero
```

Their public axiom audits are exactly:

```text
[propext, Classical.choice, Quot.sound]
```

## Exact mechanism

The proof first puts the ordinary Legendre polynomial ODE in divergence form
and applies the interval fundamental theorem of calculus.  The endpoint flux
vanishes because of the literal factor `1 - x^2`; hence every positive-degree
ordinary Legendre polynomial has interval mean zero.

Absolute coefficient summability supplies an integrable norm majorant for the
Ferrers terms.  `MeasureTheory.integral_tsum_of_summable_integral_norm` then
permits the exact exchange of interval integration and the infinite sum.  All
positive-index terms vanish, while the zeroth term integrates to twice its
coefficient.  Thus:

```text
integral[-1,1] (mode4FerrersSeries a) = 2 * a 0.
```

Consequently `a 0 != 0` forces the Ferrers series to be a nonzero function.
The accepted regular-even assembly has `0 < a 0`, so its Ferrers series is
functionally nontrivial.

This is deliberately the minimal sufficient zeroth-coefficient extraction.
It does not claim a full all-coefficient injectivity or an `L2` norm identity.

## Validation before judge dispatch

- direct `lake env lean`: PASS;
- target `lake build Q3.Proofs.RouteB.D0Mode4FerrersCoefficientExtraction`:
  PASS (`7771` jobs);
- full `lake build`: PASS (`7817` jobs);
- public axiom audit: PASS, only the three allowed standard axioms above.

The recurring `UnicodeBasic` dependency-local-change warning predates this
leaf and was not modified.

## Proshka judgment

Proshka completed its natural source audit in `5m 1s` and returned:

```text
STATUS: PROVED -- ACCEPT

isolated_two_file_commit_authorized: true
push_origin_rh_clean_authorized: true
full_coefficient_injectivity_required: false
zeroth_coefficient_extraction_sufficient: true
```

The judge matched the reviewed source SHA-256 exactly:

```text
7ab3fd05065380979963f28de0cc1557bbbc4f7875c8fbeff9f269621c2ee8e7
```

The accepted argument uses the same `S.coefficients` row, its absolute
summability, and `S.coefficient_zero_pos`.  Proshka explicitly ruled that full
all-coefficient injectivity is not required for the current consumer: the
interval integral extracting `2 * a 0` is sufficient to prove functional
nontriviality.

The next single source leaf is:

```text
G3_MODE4_FERRERS_INTERIOR_ZERO_SIMPLICITY
```

Its proposed target is
`Mode4FerrersRegularEvenProlateSolution.interior_zero_simple`, using interior
`C2`, the exact prolate ODE, positivity of `1 - x^2`, zero Cauchy data, local
ODE uniqueness, and the newly proved functional nontriviality.  It does not
yet count four zeros or identify the selected third-even mode.

## Exact evidence boundary

The theorem turns the existing normalized positive zeroth coefficient into
actual function nontriviality for the exact assembled Ferrers series.  It does
not supply the matching root, order the mode in the Sturm-Liouville spectrum,
or identify it with the source-locked degree-four / third-even PSWF.

The assembled object remains conditional on:

```text
mode4RootFunction mProject K Lambda = 0
```

## Remaining G3 chain

Still missing:

- source endpoint brackets or another unconditional matching-root supplier;
- physical-window scaling;
- degree-four / selected-third-even-mode identification;
- the mode-zero companion;
- the two restricted plus-phase finite-Fourier eigenrelations;
- construction of the actual production `ProlatePair`;
- the published CCM Lemma 7.2 rate;
- denominator floor and one coupled cofinal schedule.

G1 remains held at:

```text
G1_LITERAL_CCM_QUANTITATIVE_GAP_SOURCE_NOT_FOUND
```

## Nonclaims

```text
NO_UNCONDITIONAL_ROOT
NO_FULL_COEFFICIENT_INJECTIVITY
NO_FUNCTION_NORM_IDENTITY
NO_PHYSICAL_WINDOW_SCALING
NO_SELECTED_MODE_IDENTIFICATION
NO_MODE_ZERO
NO_FINITE_FOURIER_EIGENRELATION
NO_ACTUAL_PROLATE_PAIR
NO_LEMMA_7_2
NO_DENOMINATOR_FLOOR
NO_COFINAL_SCHEDULE
NO_G3
NO_G1
NO_ROUTE_B_PROMOTION
NO_RH
```
