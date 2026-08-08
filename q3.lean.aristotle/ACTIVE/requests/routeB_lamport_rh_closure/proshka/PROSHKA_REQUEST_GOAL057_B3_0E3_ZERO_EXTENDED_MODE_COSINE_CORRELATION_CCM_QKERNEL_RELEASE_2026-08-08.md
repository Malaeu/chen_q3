# PROSHKA REQUEST — GOAL 057 B3.0E3 ZERO-EXTENDED MODE COSINE CORRELATION / CCM Q-KERNEL RELEASE

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

`ACTIVE/requests/routeB_lamport_rh_closure/proshka/PROSHKA_VERDICT_GOAL057_B3_0E2_JOINT_ARCH_KERNEL_MODE_PRODUCT_L1_FUBINI_RELEASE_2026-08-08.md`

After B3.0E2 production validation it names the sole next discriminator:

`B3_0E3_MODE_COSINE_CORRELATION_CCM_QKERNEL_NO_SORRY_PREFLIGHT`

Its binary law is:

- PASS: return the exact harness to this chat for one production-release review;
- FAIL on factor, sign, translation, support, or index orientation: retain B3.0E
  and repair the representation.

The attached harness executes the PASS branch.

## Exact untracked harness

Repository path, intentionally untracked:

`q3.lean.aristotle/Goal057B3_0E3_Scratch.lean`

- bytes: `42746`
- lines: `1087`
- SHA-256: `1d2ef3dbc00954e853d140a5ddc92455a093f320ff1f147e8102fe17aa6e5a4f`
- hole scan `rg -n "sorry|exact\\?|admit"`: zero matches
- direct command: `lake env lean Goal057B3_0E3_Scratch.lean`
- direct exit status: `0`
- public declarations: `6` theorems
- private support declarations: `41` (`9` definitions, `32` theorems)

The direct run emits no error. It emits only linter suggestions/unused-item
warnings plus the pre-existing external warning that the local dependency
`UnicodeBasic` has changes. None is a proof failure.

The exact harness is attached to the same chat message as this request. Treat
the attachment bytes, not a reconstructed code block, as authoritative.

## Exact import closure

```lean
import Q3.Proofs.RouteB.D0PstarSourceArchKernelModeProductL1
import Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrixN1
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Convolution
```

There is no new generated PSD, Step33, hbox, numeric-payload, or direct
Aristotle-output dependency.

## Exact main theorem proved by the harness

```lean
theorem two_mul_sourceModeCosineCorrelation_eq_ccmQKernel_or_zero
    (i : PairIndex) (n r : ℤ) (x : ℝ) (hx : 0 ≤ x) :
    2 * ∫ t : ℝ,
        conj (𝓕 (logWindowZeroExtendedMode i n) t) *
          (Real.cos (2 * Real.pi * t * x) : ℂ) *
          𝓕 (logWindowZeroExtendedMode i r) t
      =
        if x ≤ L_m i then
          (Q3.RouteB.ccmQKernel (L_m i) n r x : ℂ)
        else
          0
```

The first mode is conjugated. The factor `2`, index order `(n,r)`, literal
`ccmQKernel` branches, right endpoint and outside-window zero are all retained.

## Five explicit controls proved by the harness

1. `sourceModeCosineCorrelation_control_diag_zero`: at `x=0`, `n=r`, the
   left side is exactly `2`.
2. `sourceModeCosineCorrelation_control_offdiag_zero`: at `x=0`, `n≠r`, the
   left side is exactly `0`.
3. `sourceModeCosineCorrelation_control_offdiag_inside`: for `0≤x≤L_m`,
   the literal branch is
   `(sin(2π r x/L_m)-sin(2π n x/L_m))/(pi*(n-r))`.
4. `sourceModeCosineCorrelation_control_right_boundary`: at `x=L_m`, the
   left side is exactly `0`, proved from two degenerate overlap integrals.
5. `sourceModeCosineCorrelation_control_outside_zero`: for `L_m<x`, the left
   side is exactly `0` by the zero-extension support cut.

## Proof route actually Lean-checked

1. Define the source correlation as convolution of the reflected conjugate
   first mode with the second zero-extended mode.
2. Prove the exact Fourier convolution product and the reflected-conjugate
   Fourier identity under Mathlib's cycles-per-unit convention.
3. Pay Fourier-product `L1` with two Plancherel `L2` certificates.
4. Apply pointwise Fourier inversion after proving continuity of the source
   correlation by dominated convergence.
5. Convert `2*cos` to the sum of positive and negative Fourier characters,
   giving correlation at `x` plus correlation at `-x`.
6. Rewrite both correlations as exact overlaps of the zero-extended log-window
   modes, with support intervals `[0,L_m-x]` and `[x,L_m]`.
7. Evaluate the diagonal overlaps and recover the diagonal cosine branch.
8. Evaluate the off-diagonal exponential integrals, use integer periodicity at
   `L_m`, and combine the two orientations into the literal CCM sine branch.
9. Check the deliberate denominator reversal: exponential denominators use
   `r-n`, while the CCM real branch uses `n-r`; the sine numerator reverses in
   the same calculation.
10. Prove the right boundary from degenerate overlaps and the outside branch
    from compact support, without extending `ccmQKernel` past its source window.

No one-sided half-factor, archimedean `x` integration, `ccmWREntry`, full
source Weil form, or associated operator graph is claimed.

## Print-axioms output

```text
'...two_mul_sourceModeCosineCorrelation_eq_ccmQKernel_or_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
'...sourceModeCosineCorrelation_control_right_boundary' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

No project axiom and no sorry axiom appears.

## Plants

- `P057_B3_0E3_1_FACTOR_TWO`: fail if the external factor `2` is dropped or
  moved into the wrong CCM branch.
- `P057_B3_0E3_2_ANTILINEAR_FIRST`: fail if the first mode loses conjugation
  or `(n,r)` is reversed.
- `P057_B3_0E3_3_FOURIER_CONVENTION`: fail if cycles-per-unit Mathlib Fourier
  characters are confused with angular frequency.
- `P057_B3_0E3_4_OFFDIAG_SIGN`: fail if the sine numerator or denominator is
  reversed independently.
- `P057_B3_0E3_5_LITERAL_SUPPORT`: fail if the zero extension or exact overlap
  intervals are weakened.
- `P057_B3_0E3_6_RIGHT_BOUNDARY`: fail if `x=L_m` is treated as outside or is
  not proved exactly zero.
- `P057_B3_0E3_7_NO_GENERATED_BACKEND`: fail if production adds a generated
  PSD/Step33/hbox/payload backend.

## Requested verdict

Please decide exactly one operational release in this same chat:

1. release production materialization of one new Route-B Lean file containing
   exactly the six public theorems above and at most the observed 41 private
   support declarations; or
2. reject the harness with the first exact mathematical or Lean defect, retain
   the B3.0E wall, and state the smallest repair.

If released, state:

- exact owned file;
- exact import list;
- exact public declarations;
- private-support ceiling;
- validation commands;
- success and stop codes;
- whether B3.0E3 closes after production validation;
- the exact smallest successor atom and discriminator.

Do not release one-sided CCM endpoint assembly, the full
`sourceArchimedeanModePairing = -ccmWREntry` crosswalk, any coarse Goal-057
checkpoint, promotion, PX, or RH in this transaction.

## Required labels

Every substantive claim must carry one or more of:

`[SOURCE] [LEAN] [DERIVED] [ABSTRACT] [CONDITIONAL] [NUMERIC]`
