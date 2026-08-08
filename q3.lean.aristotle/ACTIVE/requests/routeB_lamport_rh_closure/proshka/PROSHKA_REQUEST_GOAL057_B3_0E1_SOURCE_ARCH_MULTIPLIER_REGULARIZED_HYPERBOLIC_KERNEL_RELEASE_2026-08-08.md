# PROSHKA REQUEST — GOAL 057 B3.0E1 SCALAR HYPERBOLIC IDENTITY OPERATIONAL RELEASE

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

## Parent verdict

Parent verdict:

`WALL_GOAL057_B3_0E_SOURCE_ARCH_CCM_WR_BRIDGE_MISSING`

Parent artifact:

`ACTIVE/requests/routeB_lamport_rh_closure/proshka/PROSHKA_VERDICT_GOAL057_B3_0E_SOURCE_ARCHIMEDEAN_PAIRING_CCM_WR_SIGN_NORMALIZATION_CROSSWALK_2026-08-08.md`

The parent verdict selected Candidate 3 and authorized exactly one discriminator:

`B3_0E1_SCALAR_HYPERBOLIC_IDENTITY_NO_SORRY_PREFLIGHT`

Its PASS branch says:

`return_in_same_chat_for_one_operational_release`

This request executes that PASS branch.

## Exact untracked harness

Path outside the repository:

`/tmp/Goal057B3_0E1_Scratch.lean`

- bytes: `23556`
- lines: `597`
- SHA-256: `49425edef5c5b972d93f4f1c9f84877b4f9c23063fe736b06856cc0bae16af47`
- hole scan `rg -n "sorry|exact\\?|admit"`: zero matches
- direct command: `lake env lean /tmp/Goal057B3_0E1_Scratch.lean`
- direct exit status: `0`
- stdout/stderr bytes: `1421`
- stdout/stderr lines: `26`
- stdout/stderr SHA-256: `f77159b262cf159480b682f7433afd1b2b3f5d75f023ca5ba2cd0876cd2fd46f`

The exact harness is attached to the same chat message as this request. Treat the attachment bytes, not a reconstructed code block, as authoritative.

## Exact import closure

The harness has one explicit import:

```lean
import Q3.Proofs.RouteB.D0PstarExactArchSymbolLogDomination
```

It compiles with that sole explicit import. There is no generated PSD, Step33, hbox, or numeric-payload dependency.

## Exact public surface proved by the harness

```lean
def sourceArchimedeanRegularizedKernel (t x : ℝ) : ℝ :=
  (Real.exp (x / 2) * Real.cos (2 * Real.pi * t * x) - Real.exp (-x)) /
    (Real.exp x - Real.exp (-x))

theorem sourceArchimedeanRegularizedKernel_integrableOn (t : ℝ) :
    IntegrableOn (sourceArchimedeanRegularizedKernel t) (Set.Ioi 0)

theorem sourceArchimedeanMultiplier_eq_regularizedHyperbolicIntegral
    (t : ℝ) :
    sourceArchimedeanMultiplier t =
      -Real.log Real.pi - Real.eulerMascheroniConstant -
        2 * ∫ x in Set.Ioi 0, sourceArchimedeanRegularizedKernel t x
```

Exactly three public declarations are proposed. All support declarations in the harness are private.

## Proof route actually Lean-checked

1. Prove the real Laplace-cosine atom from Mathlib's complex exponential integral:
   `∫₀∞ exp (-a x) cos (b x) dx = a / (a² + b²)` for `0 < a`.
2. Keep the paired numerator
   `exp (-u) - exp (-u/4) * cos (pi*t*u)` intact.
3. Expose the removable zero-endpoint singularity by quotient-of-slopes and obtain a continuous extension on the compact near-zero interval.
4. Prove the tail bound by the integrable majorant
   `(1-exp(-1))⁻¹ * (exp(-u) + exp(-u/4))` on `u > 1`.
5. Rewrite each real digamma-series term as the paired Laplace term
   `exp(-(n+1)u) - exp(-(n+1/4)u) cos(pi*t*u)`.
6. Sum the paired terms geometrically before estimating.
7. Use `MeasureTheory.hasSum_integral_of_dominated_convergence` for the integral/tsum exchange.
8. The pointwise L¹ majorant is the norm series of the paired terms; its sum is exactly the norm of the already-proved integrable regularized quotient.
9. Consume `Q3.re_digamma_eq_sum_of_tendsto` and `Q3.digammaSeq_tendsto_Q3_digamma`.
10. Apply the exact change of variables `u = 2*x`; this produces the final minus sign and factor `2`.

No factorwise near-zero domination is used.

## Print-axioms output

```text
'...sourceArchimedeanRegularizedKernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'...sourceArchimedeanRegularizedKernel_integrableOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'...sourceArchimedeanMultiplier_eq_regularizedHyperbolicIntegral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

No project axiom and no sorry axiom appears.

## Plants

- `P057_B3_0E1_1_PAIRED_ENDPOINT_CANCELLATION`: fail if the two numerator terms are dominated separately near zero.
- `P057_B3_0E1_2_FINAL_MINUS_AND_TWO`: fail if the `u = 2*x` transport loses the final minus sign or factor `2`.
- `P057_B3_0E1_3_NO_GENERATED_BACKEND`: fail if production imports any generated PSD/Step33/hbox/payload backend.

## Requested verdict

Please decide exactly one operational release in this same chat:

1. release production materialization of
   `Q3/Proofs/RouteB/D0PstarSourceArchHyperbolicKernel.lean`
   with the exact three-declaration public surface above and a stated private-support budget; or
2. reject the harness with the first exact mathematical or Lean defect and retain the wall.

If released, state:

- exact owned file;
- exact import list;
- exact public declarations;
- private-support budget;
- validation commands;
- success and stop codes;
- whether B3.0E1 closes and whether B3.0E2 becomes the next open atom;
- the exact next discriminator after production validation.

Do not release B3.0E2 or the full CCM crosswalk in this transaction.

## Required labels

Every substantive claim must carry one or more of:

`[SOURCE] [LEAN] [DERIVED] [ABSTRACT] [CONDITIONAL] [NUMERIC]`

