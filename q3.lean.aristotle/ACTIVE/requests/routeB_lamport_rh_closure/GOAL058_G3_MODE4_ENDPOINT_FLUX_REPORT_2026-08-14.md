# Goal 058 G3 mode-four endpoint-flux report

Date: 2026-08-14

Lane: `CHALLENGER / NOT_RH`

Execution pin confirmed by Proshka in the living phase chat:

```text
HEAD = origin/rh_clean = d9df5f9c2b07caf853a1e939a0ae1cc402b709fa
P9_STRICT_PASS
Route B CHECK: OK
```

The Lean file and this report were kept uncommitted and unpushed through the
bounded execution and validation phase, exactly as the corrected judge
directive required.

## Result

```text
G3_MODE4_FERRERS_ENDPOINT_FLUX_PROVED
```

The exact tail-spliced mode-four Ferrers source row now satisfies

```text
(1 - x^2) y'(x) -> 0  as x ->  1 from below,
(1 - x^2) y'(x) -> 0  as x -> -1 from above.
```

The public supplier is:

```text
Q3.RouteB.mode4Ferrers_zeroFlux_at_endpoints_of_tail_splice
```

Its theorem head is the byte-prescribed head from the Proshka verdict.  It
retains the exact `mProject/K/Lambda` source family, separation hypotheses and
literal `mode4TailCoefficientRow` splice.

## Public heads

- `Q3.RouteB.mode4Ferrers_fluxTerm_abs_le`
- `Q3.RouteB.mode4Ferrers_fluxSeries_tendsto_zero_at_one`
- `Q3.RouteB.mode4Ferrers_fluxSeries_tendsto_zero_at_neg_one`
- `Q3.RouteB.mode4Ferrers_zeroFlux_at_endpoints_of_tail_splice`

All four print exactly:

```text
[propext, Classical.choice, Quot.sound]
```

## Proof mechanism

For `P_(2q)`, the committed ordinary-Legendre energy bound gives a global
closed-window estimate on the natural flux.  After multiplying once more by
the nonnegative endpoint factor and taking square roots, the implemented
majorant is

```text
|(1 - x^2) * mode4FerrersFirstDerivativeTerm a q x|
  <= 4 * (q + 1) * |a q|,        x in [-1,1].
```

The exact tail splice supplies summability of `(q+1)|a q|` through
`mode4RecurrenceRow_polynomiallyWeighted_abs_summable_of_tail_splice` at
weight `r=1`.  Each fixed polynomial flux term tends to zero at either
endpoint.  Mathlib's Tannery theorem then passes those pointwise limits
through the `tsum` under the proved weighted majorant.

The proof does not use the prolate ODE, a matching root, a mode index, an
endpoint hypothesis, or any rate/gap/floor binder.

## Planted falsifiers

All four required guards compile in the owned Lean file.

1. `G3_MODE4_ENDPOINT_FACTOR_MUTATION_SURVIVED`
   - The finite row supported at `q=1` is instantiated explicitly.
   - `P_2'(1)=3` is derived from the committed three-term recurrence.
   - Replacing `1-x^2` by `1+x^2` is proved nonzero at `x=1`.

2. `G3_INTERIOR_C2_NOT_ENDPOINT_DOMAIN`
   - The field `(1-x^2)^(-1)` is proved `ContDiffOn R 2` on `(-1,1)`.
   - Its natural flux is identically `1`, so it is formally proved not to
     tend to zero at the right endpoint.

3. `G3_L2_TO_WEIGHTED_L1_SHORTCUT`
   - The row `a_q=(q+1)^(-2)` is proved square summable.
   - Its weighted absolute row `(q+1)|a_q|=(q+1)^(-1)` is proved
     nonsummable by the harmonic-series theorem.

4. `G3_MODE4_SOURCE_ROW_DROPPED`
   - A named compile-time guard consumes the literal tail splice and exact
     polynomially weighted supplier at `r=1`.
   - The public theorem also exposes that same splice in its theorem head;
     an arbitrary coefficient row is not relabelled as the source row.

## Validation

- direct `lake env lean Q3/Proofs/RouteB/D0Mode4FerrersEndpointFlux.lean`:
  PASS;
- target `lake build Q3.Proofs.RouteB.D0Mode4FerrersEndpointFlux`:
  PASS (`7769` jobs);
- full `lake build`: PASS (`7817` jobs);
- `bash scripts/q3_check.sh .../D0Mode4FerrersEndpointFlux.lean`:
  PASS (`q3_check ok`);
- forbidden `sorry`/`admit`/`exact?`/`native_decide`/new `axiom`/`opaque`
  scan: PASS;
- forbidden G1/G3 source-binder scan: PASS;
- `git diff --check`: PASS.

The recurring `UnicodeBasic` dependency-local-change warning predates this
leaf and was not modified.

## Proshka judgment

The result was returned to the same living Goal 058 phase chat.  Proshka
completed its natural review in `6m 2s` and returned:

```text
ACCEPT

Commit and push: AUTHORIZED for an isolated two-file commit containing only
D0Mode4FerrersEndpointFlux.lean and
GOAL058_G3_MODE4_ENDPOINT_FLUX_REPORT_2026-08-14.md.
```

The next single source leaf is:

```text
G3_MODE4_FERRERS_REGULAR_EVEN_PROLATE_SOLUTION_ASSEMBLY
```

Its scope is only to assemble the already proved normalized nonzero/even
Ferrers series, closed-interval continuity, interior `C^2`, exact prolate ODE,
and the new two-endpoint zero-flux theorem into one public regular even prolate
solution conditional on the matching root.  Ordered `psi_4` / third-even
identification remains outside that leaf.

## Remaining boundary

This removes one endpoint-domain ambiguity from the mode-four source
constructor.  It does not supply the remaining actual-mode chain.  In
particular, the constructor is still conditional on a matching root and still
lacks physical-window scaling, third-even/degree-four selection, the mode-zero
companion, restricted plus-phase finite-Fourier eigenrelations, the actual
production pair, the quantitative source rate, denominator floor and coupled
cofinal schedule.

G1 remains held at:

```text
G1_LITERAL_CCM_QUANTITATIVE_GAP_SOURCE_NOT_FOUND
```

## Nonclaims

```text
NO_UNCONDITIONAL_ROOT
NO_SOURCE_ENDPOINT_BRACKET
NO_PHYSICAL_WINDOW_SCALING
NO_THIRD_EVEN_SELECTION
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
