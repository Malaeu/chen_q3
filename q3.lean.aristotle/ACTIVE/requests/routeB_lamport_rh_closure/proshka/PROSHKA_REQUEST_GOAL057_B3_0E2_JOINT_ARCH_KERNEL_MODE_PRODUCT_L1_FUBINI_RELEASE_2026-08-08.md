# PROSHKA REQUEST — GOAL 057 B3.0E2 JOINT ARCH KERNEL-MODE L1/FUBINI OPERATIONAL RELEASE

Date: 2026-08-08
Route: Route B (`CHALLENGER_NOT_RH`)
Goal: 057
Phase key: unchanged; continue the same living Proshka chat
Requested action: one operational release decision after a passing discriminator

## Boundaries

- `BUS_010: VOID`
- `GOAL_055: HOLD`
- `G2_CCM: FROZEN`
- `PX_RH_CLAIM: NOT_MADE`
- no promotion and no RH claim
- do not click or use any shortcut answer button
- no production mutation is requested before this release decision

## Parent verdict and exact discriminator

Parent verdict artifact:

`ACTIVE/requests/routeB_lamport_rh_closure/proshka/PROSHKA_VERDICT_GOAL057_B3_0E1_SOURCE_ARCH_MULTIPLIER_REGULARIZED_HYPERBOLIC_KERNEL_RELEASE_2026-08-08.md`

After B3.0E1 production validation it names the sole next discriminator:

`B3_0E2_JOINT_ARCH_KERNEL_MODE_PRODUCT_L1_FUBINI_NO_SORRY_PREFLIGHT`

Its binary law is:

- PASS: B3.0E2 becomes executable in one later same-chat release;
- FAIL because no cancellation-preserving product majorant exists: retain the
  B3.0E wall, do not exchange integrals, and shift to a source-distribution-
  action representation.

The attached harness executes the PASS branch.

## Exact untracked harness

Path outside the repository:

`/tmp/Goal057B3_0E2_Scratch.lean`

- bytes: `27927`
- lines: `696`
- SHA-256: `1ff1ef467028a6a62a9d2722c2b96e0ec6aff94366645e32bab91ff5f82f7bde`
- hole scan `rg -n "sorry|exact\\?|admit"`: zero matches
- direct command: `lake env lean /tmp/Goal057B3_0E2_Scratch.lean`
- direct exit status: `0`
- public declarations: `2`
- private support declarations: `22` (`4` definitions, `18` theorems)

The direct run emits only the pre-existing external warning that the local
Mathlib dependency `UnicodeBasic` has changes.  The harness itself emits no
warning or error.

The exact harness is attached to the same chat message as this request. Treat
the attachment bytes, not a reconstructed code block, as authoritative.

## Exact import closure

```lean
import Q3.Proofs.RouteB.D0PstarSourceArchHyperbolicKernel
import Q3.Proofs.RouteB.D0PstarVModeLogWeightedL2
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
```

There is no generated PSD, Step33, hbox, numeric-payload, or Aristotle output
dependency.

## Exact public surface proved by the harness

```lean
def sourceArchimedeanKernelModeIntegrand
    (i : PairIndex) (n r : ℤ) (p : ℝ × ℝ) : ℂ :=
  conj (𝓕 (logWindowZeroExtendedMode i n) p.1) *
    (sourceArchimedeanRegularizedKernel p.1 p.2 : ℂ) *
    𝓕 (logWindowZeroExtendedMode i r) p.1

theorem sourceArchimedeanKernelModeIntegrand_integrable
    (i : PairIndex) (n r : ℤ) :
    Integrable (sourceArchimedeanKernelModeIntegrand i n r)
      (volume.prod (volume.restrict (Set.Ioi 0)))
```

The first mode is conjugated, exactly preserving the established
antilinear-first `(n,r)` convention.  The `x` measure is literally restricted
to `Ioi 0`; no endpoint atom or implicit extension is claimed.

## Proof route actually Lean-checked

1. Preserve the B3.0E1 paired-kernel normalization exactly.
2. Prove `|1 - cos y| <= 2*sqrt |y|` by combining the quadratic Taylor bound
   and the global bound `<= 2`; no numerical approximation is used.
3. Prove the denominator lower bound
   `2*x*exp(-2*x) <= 1-exp(-2*x)` from `1+z <= exp z`.
4. Rewrite the paired numerator as the regular exponential difference plus
   `exp(-x/2)*(1-cos(2*pi*t*x))`; the two original singular terms are never
   separately dominated.
5. On `0 < x <= 1`, derive
   `norm K(t,x) <= 1 + exp(3/2)*sqrt|2*pi*t|/sqrt x`.
   Thus the endpoint cost is the integrable factor `x^(-1/2)` and the
   frequency cost is only `sqrt|t|`.
6. Use the already-proved resonance-safe fixed-mode decay
   `norm V(i,n,t) <= C(i,n)/(1+|t|)` twice.  The weighted mode product is
   dominated by a constant times `(1+|t|)^(-3/2)`, hence is in `L1`.
7. On `x > 1`, dominate the kernel by
   `(1-exp(-2))^-1*(exp(-2*x)+exp(-x/2))`, independently of `t`.
8. Build the near and tail carriers with `Integrable.mul_prod` and strong
   measurability of the literal complex integrand.
9. Union `univ × Ioc 0 1` with `univ × Ioi 1`, using the exact identity
   `Ioc 0 1 ∪ Ioi 1 = Ioi 0`.
10. Convert the resulting `IntegrableOn` certificate back to the exact product
    measure `volume.prod (volume.restrict (Ioi 0))`.

The proof does not need the sharper provisional logarithmic kernel-norm
estimate.  The honest square-root frequency cost is already paid by the two
fixed-mode `1/(1+|t|)` decays.

## Print-axioms output

```text
'...sourceArchimedeanKernelModeIntegrand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'...sourceArchimedeanKernelModeIntegrand_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

No project axiom and no sorry axiom appears.

## Plants

- `P057_B3_0E2_1_ANTILINEAR_FIRST`: fail if the first mode is not conjugated
  or the `(n,r)` order changes.
- `P057_B3_0E2_2_PAIRED_ENDPOINT`: fail if the original singular kernel terms
  are separately dominated near zero.
- `P057_B3_0E2_3_SQRT_ENDPOINT`: fail if the near majorant loses the integrable
  `x^(-1/2)` endpoint exponent.
- `P057_B3_0E2_4_MODE_DECAY_PAYS_FREQUENCY`: fail if both fixed-mode decay
  estimates are not used to pay the `sqrt|t|` cost.
- `P057_B3_0E2_5_LITERAL_POSITIVE_X_MEASURE`: fail if `Ioi 0`, the product
  measure, or the near/tail union is weakened or relabelled.
- `P057_B3_0E2_6_NO_GENERATED_BACKEND`: fail if production imports a generated
  PSD/Step33/hbox/payload backend.

## Requested verdict

Please decide exactly one operational release in this same chat:

1. release production materialization of one new Route-B Lean file containing
   exactly the two public declarations above and at most the observed 22
   private support declarations; or
2. reject the harness with the first exact mathematical or Lean defect, retain
   the B3.0E wall, forbid Fubini, and select the source-distribution-action
   fallback.

If released, state:

- exact owned file;
- exact import list;
- exact public declarations;
- private-support ceiling;
- validation commands;
- success and stop codes;
- whether B3.0E2 closes after production validation;
- the exact smallest B3.0E3 atom and discriminator.

Do not release B3.0E3, mode-correlation equality, one-sided CCM endpoint
assembly, the full `sourceArchimedeanModePairing = -ccmWREntry` crosswalk, any
coarse Goal-057 checkpoint, promotion, PX, or RH in this transaction.

## Required labels

Every substantive claim must carry one or more of:

`[SOURCE] [LEAN] [DERIVED] [ABSTRACT] [CONDITIONAL] [NUMERIC]`
