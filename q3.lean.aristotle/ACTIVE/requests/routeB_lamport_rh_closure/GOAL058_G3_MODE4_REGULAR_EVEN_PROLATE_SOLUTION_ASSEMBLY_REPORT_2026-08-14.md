# Goal 058 G3 mode-four regular-even solution assembly report

Date: 2026-08-14

Lane: `CHALLENGER / NOT_RH`

Execution base:

```text
HEAD = origin/rh_clean = 9677b5f2
P9_STRICT_PASS
Route B CHECK: OK
```

The Lean file and this report were kept uncommitted and unpushed through the
bounded execution and validation phase pending review in the living Goal 058
Proshka chat.

## Result

```text
G3_MODE4_FERRERS_REGULAR_EVEN_PROLATE_SOLUTION_ASSEMBLED
```

Owned Lean file:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0Mode4FerrersRegularEvenProlateSolution.lean
```

Direct import:

```text
Q3.Proofs.RouteB.D0Mode4FerrersEndpointFlux
```

## Public surface

The new public structure is:

```text
Q3.RouteB.Mode4FerrersRegularEvenProlateSolution
```

The root-conditional constructor is:

```text
Q3.RouteB.exists_mode4FerrersRegularEvenProlateSolution_of_root
```

Its public axiom audit is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

## Assembled fields

For the exact source parameters `mProject`, `K`, and `Lambda`, the structure
retains one coefficient row and all of the following kernel-checked facts:

- `0 < a 0` and `a != 0`;
- absolute and square summability;
- the exact weighted normalization with sum `1`;
- the literal PSWF-Legendre recurrence;
- the nonzero splice anchor and literal committed tail splice;
- evenness of `mode4FerrersSeries a`;
- continuity on `[-1,1]`;
- `ContDiffOn R 2` on `(-1,1)`;
- the exact dimensionless prolate ODE on `(-1,1)`;
- natural zero flux at both singular endpoints.

The constructor takes the committed matching-root equation as an input and
derives every assembled field from existing public suppliers.  No regularity,
ODE, endpoint, ordered-mode, Fourier, rate, gap, or denominator conclusion is
introduced as a binder.

## Validation

- direct `lake env lean`: PASS;
- target
  `lake build Q3.Proofs.RouteB.D0Mode4FerrersRegularEvenProlateSolution`:
  PASS (`7770` jobs);
- full `lake build`: PASS (`7817` jobs);
- `bash scripts/q3_check.sh ...`: PASS (`q3_check ok`);
- forbidden proof-hole and new-axiom scan: PASS;
- forbidden downstream-source-binder scan: PASS;
- `git diff --check`: PASS.

The recurring `UnicodeBasic` dependency-local-change warning predates this
leaf and was not modified.

## Proshka judgment

Proshka completed its natural review in `5m 28s` and returned:

```text
ACCEPT

Commit and push: AUTHORIZED for an isolated two-file commit containing only
D0Mode4FerrersRegularEvenProlateSolution.lean and
GOAL058_G3_MODE4_REGULAR_EVEN_PROLATE_SOLUTION_ASSEMBLY_REPORT_2026-08-14.md.
```

The judge explicitly accepted coefficient-row nontriviality as sufficient for
this assembly leaf and for commit.  The assembly theorem does not assert the
functional equality `mode4FerrersSeries a != 0`, and no such claim is required
before this commit.

The next single source leaf is:

```text
G3_MODE4_FERRERS_FUNCTION_NONZERO_FROM_COEFFICIENT_EXTRACTION
```

It must establish injectivity/coefficient extraction for the current
absolutely summable even Ferrers series and derive function nontriviality from
the normalized nonzero coefficient row before ordered mode identification.

## Exact evidence boundary

The formal nontriviality field is the nonzero normalized coefficient row.  A
separate coefficient-extraction theorem identifying nonzero row norm with a
nonzero function norm has not been invented in this assembly leaf.

The object is conditional on:

```text
mode4RootFunction mProject K Lambda = 0
```

It is still a dimensionless mode-four source object.  It is not yet the
ordered selected production mode and it is not a field of the unchanged
`ProlatePair` production record.

## Remaining G3 chain

Still missing:

- source endpoint brackets or another unconditional matching-root supplier;
- physical-window scaling;
- degree-four / selected-even-mode identification;
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
NO_FUNCTION_NORM_EXTRACTION
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
