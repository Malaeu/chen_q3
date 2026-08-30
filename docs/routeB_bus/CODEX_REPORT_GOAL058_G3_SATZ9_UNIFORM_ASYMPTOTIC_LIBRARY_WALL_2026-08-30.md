# STATUS: CONDITIONAL — exact Satz-9 source objects elaborate; the uniform asymptotic is absent from Lean

```yaml
schema: q3_goal058_g3_satz9_source_attempt.v1
date: 2026-08-30
executor: CODEX_MAC
task: G3_MEIXNER_SCHAEFKE_SELECTED_SATZ9_RATE_SOURCE
verdict_commit: ac8dec55094426e021e36b40461b773599e8a448
verdict_blob: 768173802446a04663f827d4bdb77e5d1e508cf2
result: G3_SATZ9_UNIFORM_ASYMPTOTIC_LIBRARY_WALL
lean_edit_performed: false
route_promotion: false
px_rh_claim: NOT_MADE
```

## Outcome

The frozen public theorem head was typechecked in an isolated Lean harness. The
source-object and parameter layers are compatible: for each `k`, both
`Satz9SourceData` packages are constructed from the same source-pure
`BookRegularEvenSpectrumEven (mode4JacobiG (k + 2))` package using
`selectedSatz9SourceData_at_projectTheta_degree_zero_four`.

After those witnesses are constructed, Lean leaves exactly the following goal:

```lean
exists C0 C4,
  0 <= C0 and 0 <= C4 and
  (forall_eventually k in Filter.atTop,
    forall x in Set.Icc
        (-(selectedFerrersPaperLambda k))
        (selectedFerrersPaperLambda k),
      norm (centerNormalized (S0 k).p x -
        ((parabolicCylinderD 0 (projectCylinderArgument x) : Real) : Complex)) <=
          C0 / selectedFerrersPaperGamma k and
      norm ((3 : Complex) * centerNormalized (S4 k).p x -
        ((parabolicCylinderD 4 (projectCylinderArgument x) : Real) : Complex)) <=
          C4 / selectedFerrersPaperGamma k)
```

The first failed proof point is
`/tmp/G6N1MeixnerSchaefkeSelectedSatz9RateSourceHarness.lean:46:51`.
Lines 48--61 of that harness construct `S0` and `S4`; no earlier object, import,
parameter, coercion, normalization, or binder mismatch remains. The direct-import
list in the verdict required one mechanical API repair: the harness imports
`G6N1SelectedSatz9SourcePackageTransport`, which supplies the already-ratified
same-package construction.

## Exact missing analytic lemma

The missing lemma is the fixed-mode, center-normalized uniform consequence of
Meixner--Schaefke Satz 9 for modes `n = 0` and `n = 4`, with constants independent
of `k`, after the exact substitution

```text
gamma_MS = selectedFerrersPaperGamma k = 2*pi*lambda_k^2,
z = x/lambda_k,
x in [-lambda_k, lambda_k].
```

It must prove the displayed eventual pair of `C0/gamma_k` and `C4/gamma_k`
bounds from the source ODE/regular-first-kind construction itself. No theorem in
the current environment supplies this estimate.

The nearest existing result,
`centerNormalizedSatz9Rate_of_scaledFixedModeRate`, starts only after an
explicit raw uniform rate and a denominator guard have been assumed. Using it
here would merely restate the missing theorem as a hypothesis and is forbidden
by the operative verdict.

## Source fragment represented

Meixner--Schaefke, section 3.2, Satz 9, printed page 243 (PDF page 255), gives
uniformly for `z in [-1,1]` and fixed `m,n`

```text
ps_n^m(z; gamma^2)
  = (-1)^m * (4*gamma/pi)^(1/4) / (n-m)!
      * sqrt((n+m)!/(2*n+1))
      * (1-z^2)^(m/2)
      * D_(n-m)(sqrt(2*gamma)*z)
      + O(gamma^(-3/4)).
```

For `m = 0`, dividing by the mode's own leading
`(4*gamma/pi)^(1/4)` scale converts the raw remainder to
`O(gamma^(-1))`. The frozen degree-zero and degree-four normalizations are the
ones encoded in the theorem head, including the factor `3` in the degree-four
row. The repository usage card records this as a paper theorem and explicitly
states that it is not yet a Lean supplier.

## Search and validation ledger

1. `lake env lean /tmp/G6N1MeixnerSchaefkeSelectedSatz9RateSourceHarness.lean`
   elaborated the frozen theorem head and same-package witness construction,
   then stopped only at the uniform-rate goal above.
2. `./ask.sh "Meixner Schaefke Satz 9 fixed mode uniform center normalized rate gamma inverse" --deep`
   searched all eight registered shelves. Q3 returned only the conditional
   rate consumer and source-package interfaces; the enabled external Lean base
   `zeta23` returned unrelated textual candidates and no exact declaration.
3. `scripts/supplier_preflight.py` was run after a complete fresh Route B
   elaborated-environment rebuild. Its closed result is recorded below.

```yaml
supplier_preflight_status: COMPLETE_ABSENCE
supplier_preflight_reason: >-
  candidate declaration is absent from the complete local Route B environment,
  Lean core/Q3/dependency source trees, and every enabled external Lean base;
  prose retrieval candidates do not establish a declaration
routeb_source_modules: 371
routeb_current_built_modules: 371
routeb_indexed_declarations: 3369
routeb_stale_modules: 0
routeb_never_built_modules: 0
routeb_sorryAx_declarations: 0
routeb_other_axiom_declarations: 0
external_lean_bases:
  enabled: [zeta23]
  errors: []
```

## Frozen boundary

- No `G6N1MeixnerSchaefkeSelectedSatz9RateSource.lean` was added: a file whose
  proof merely accepts the rate as a premise would be fake progress.
- No `sorry`, `admit`, axiom, fitted constant, numerical surrogate, independent
  `S0`/`S4` package, denominator-floor wrapper, or conditional receiver was
  introduced.
- This report does not close the Satz-9 theorem, the Fuchs source rate, theta
  rate, H2a, Goal 058, Route B, or RH.

AUTOPSY: dropped=DEPENDENCY; note=shape=UNIFORM_ASYMPTOTIC_LIBRARY_WALL | source objects and exact units elaborate, but no Lean theorem proves the fixed-mode Satz-9 uniform O(gamma^-1) estimate
