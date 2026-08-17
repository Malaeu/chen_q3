# STATUS: CONDITIONAL — KERNEL REPAIR COMMITTED; CANONICAL REBUILD REQUIRED
```yaml
PRIMARY: FERRERS_FOURIER_SCALAR_SIGN_KERNEL_REPAIR
PRIMARY_COUNT: 1

SOURCE_FAIL:
  COMMIT: 83f2583c791a318add718b9a5db459a79830ee79
  ORIGINAL_NODE: c4d1d98fddfb634dad050afc3959955b6de886e3
  FAILURE: "simp made no progress at line 47"
  SORRYAX_PRESENT: true

REPAIR:
  COMMIT: 8c8c885724e49dd3372ad26f11dc9207bdbf8efd
  FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FerrersPhysicalFourierScalarSign.lean
  PATCH_SCOPE: ONE_PROOF_STEP_ONLY
  MATHEMATICAL_STATEMENT_CHANGED: false
  PUBLIC_SURFACE_CHANGED: false
  NEW_AXIOM_DECLARATION: false
  KERNEL_CHECK: PENDING

REPAIR_MECHANISM:
  OLD: brittle_simpa_after_integral_comp_div
  NEW: explicit_change_to_scaled_integral_then_exact_hscale
  EXACT_REFERENCE: intervalIntegral.integral_comp_div

ARSENAL_MANDATE: ACCEPTED
ARSENAL_CARDS_USED: []

ROUTE_EFFECT:
  scalar_sign_relation: CONDITIONAL_PENDING_KERNEL
  center_sign_reduction: CONDITIONAL_PENDING_KERNEL
  center_pos_of_no_interior_zero: NOT_STARTED
  G3: OPEN
  G1: OPEN

SCOPE: ABSTRACT
VERIFIER: CONDITIONAL
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
RH_CLAIM: false

SUCCESS_CODE: FERRERS_FOURIER_SCALAR_SIGN_KERNEL_GREEN
FAILURE_CODE: FERRERS_FOURIER_SCALAR_SIGN_KERNEL_REPAIR_STILL_FAILS
```

## ROUTE MAP

The kernel failure was isolated to the local conversion from the exact interval
scaling theorem to the physical-series integral.  The source theorem has exact
shape

```lean
(∫ x in a..b, f (x / c)) = c • ∫ x in a / c..b / c, f x
```

and the preceding rewrites already replace the scaled endpoints by `-1, 1` and
the source integral by `2 * S.coefficients 0`.

The failed `simpa` attempted to unfold definitions after the expression was
already definitionally in the target coordinates.  The repair makes the target
explicit and applies `hscale` directly:

```lean
change
  (∫ u in (-s)..s,
    mode4FerrersSeries S.coefficients (u / s)) =
    s * (2 * S.coefficients 0)
exact hscale
```

This preserves the source object, interval, scale, normalization and theorem
heads.  `[ABSTRACT][CONDITIONAL]`

## FINAL PROPOSAL

Registered prediction:

```text
P058-SIGN-REPAIR:
  the explicit target change closes the original line-47 failure;
  no mathematical supplier is missing.
```

Cheapest decisive test:

```bash
cd q3.lean.aristotle
lake build Q3.Proofs.RouteB.D0Mode4FerrersPhysicalFourierScalarSign
```

Required success evidence:

```text
1. target build exits 0;
2. neither public theorem depends on sorryAx;
3. #print axioms returns exactly
   [propext, Classical.choice, Quot.sound]
   for both public theorems.
```

Only after this gate is green may the route start
`center_pos_of_no_interior_zero`.

## STRONGEST ATTACK

The strongest remaining objection is technical:

> `exact hscale` may expose a second definitional mismatch between scalar
> multiplication and real multiplication, or a later simplification may fail
> once line 47 is repaired.

This does not invalidate the mathematical identity.  If the new line fails,
the weakest repair is to change the type of `hscale` explicitly at the local
hypothesis, not to add a new theorem, assumption, axiom, or alternate Fourier
normalization.

Forbidden repairs:

```text
- no `sorry` or `admit`;
- no theorem weakening;
- no replacement of the physical Ferrers source;
- no fitted scalar;
- no inference of center positivity;
- no G3 or RH promotion.
```

## KERNEL DIRECTIVE

```text
TASK:
Rebuild only
Q3.Proofs.RouteB.D0Mode4FerrersPhysicalFourierScalarSign
at commit 8c8c885724e49dd3372ad26f11dc9207bdbf8efd.

RETURN:
- exact stdout/stderr;
- exit code;
- both `depends on axioms` lines;
- exact next error location if the build remains red.

SUCCESS:
FERRERS_FOURIER_SCALAR_SIGN_KERNEL_GREEN

STOP:
FERRERS_FOURIER_SCALAR_SIGN_KERNEL_REPAIR_STILL_FAILS
```

## META CLOSEOUT

**What became smaller?**

The failure is no longer “the Fourier sign theorem does not compile.”  It is a
single canonical rebuild of a one-step definitional repair.

**What was killed?**

The brittle `simpa` conversion at line 47.

**What must not be tried again?**

Do not infer proof health from a text scan for `sorry`; inspect the axiom
profile after every failed build.

**Current smallest named gap:**

```text
FERRERS_FOURIER_SCALAR_SIGN_CANONICAL_REBUILD
```

**Next cheapest decisive test:**

The single target build above.

**Fate of the prior prediction:**

```text
"The failure is technique, not mathematics":
  still plausible, not yet confirmed by the kernel.
```

```yaml
iteration:
  target: Ferrers Fourier scalar sign kernel repair
  status: PROGRESS
  failed_strategy: brittle_simpa_definition_unfold
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: FERRERS_FOURIER_SCALAR_SIGN_CANONICAL_REBUILD
  invariant_learned: failed tactics can inject sorryAx without literal sorry text
  forbidden_future_move: continue downstream before axiom-clean target build
  next_decisive_test: lake_build_single_target_and_print_axioms
  progress_class: PROOF_PROGRESS
  route_score: 5
```
