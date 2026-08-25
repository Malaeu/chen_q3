# STATUS: OPEN — WRONG-SURROGATE GROWTH KILL RETRACTED; SIGNED W5 BUDGET IS LIVE

```yaml
PRIMARY: RETRACT_W5_L1_GROWTH_KILL_WRONG_SURROGATE
QUEUE_PIN: 3a6ba17fac54a443a8674d35816bafd73d8904aa

OLD_PROBE:
  object: sum_n_abs_H_nu
  verdict: INVALID_FOR_ESTAR
  prior_prediction_Ck_growth: REFUTED
  prior_kill_sup_Ck_finite_unreachable: RETRACTED

EXACT_TARGET:
  object: abs_sum_n_H_nu
  zero_mass_cancellation: LOAD_BEARING

CURRENT_EVIDENCE:
  seam:
    status: LEAN_PROVED_CONDITIONAL_ON_F72_6_INPUTS
    rate: O((k+2)^(-1/4))
  L1:
    status: NUMERIC_SIGN_CORRECT_PROBE
    observed: 0.1242802_across_k_1e3_to_1e6
  derivative:
    status: NUMERIC_SIGN_CORRECT_PROBE
    observed: 0.4467_constant_scale
  endpoint0:
    status: NUMERIC_SIGN_CORRECT_PROBE
    observed: order_1e-15
  endpointL:
    status: NUMERIC_SIGN_CORRECT_PROBE
    observed: zero_compatible

W5_EXACT_CK:
  definition: "2 * (L1_k + (Derivative_k + Jump_k)/(2*pi))"
  uniform_boundedness: PLAUSIBLE_NOT_PROVED
  cofinal_rate_kill: false

NEXT_LOAD_BEARING_GAP: W5_SIGNED_ESTAR_L1_AND_DERIVATIVE_COFINAL_BOUND
DISCRIMINATOR: PROOF_GRADE_SIGNED_ESTAR_UNIFORM_ENVELOPE

ARSENAL_MANDATE: ACCEPTED_NO_LIVE_SIDECAR_MUTATION
CARDS_APPLIED:
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C13_RESTORE_SYMMETRY_BY_EXPLICIT_SHADOW

SCOPE: COFINAL_FAMILY
VERIFIER: CONDITIONAL
PROGRESS_CLASS: FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

The Linux retraction is accepted exactly as written. The old numerical object

\[
\sum_n |H(nu)|
\]

is not the inversion-symmetric `E_star` target

\[
\left|\sum_n H(nu)\right|.
\]

Moving the modulus inside the sum destroys the cancellation supplied by zero mass. Therefore the earlier numerical growth `~ sqrt(lambda)` is evidence about a strict triangle-inequality surrogate, not about the W5 consumer. This instantiates **C10 FUNCTIONAL-NOT-SURROGATE**: the failed kill measured the wrong functional.

The queue at `3a6ba17f` records the same correction: `sum|H|` grows while `|sum H|` is numerically near cancellation floor, and the recomputed L1 probe is constant across four decades. The earlier conclusion that `C_k ~ (k+2)^(1/4)` and hence `sup_k C_k < infinity` is unreachable is therefore withdrawn, not repaired.

The seam result remains valid independently: commit `ac43234e9638ea9f748d89c2457323ab4f69cfeb` proves the repaired internal seam sum is eventually bounded by `2*(C+132)/sqrt(lambda_k)`, hence `O((k+2)^(-1/4))`, conditional on the stated F72.6 mode/chi rate input. It explicitly does not control L1, derivative, or endpoint components.

The exact W5 Fourier-decay budget is

\[
C_k=2\left(L1_k+\frac{Derivative_k+Jump_k}{2\pi}\right).
\]

Thus the new sign-correct probes are fully compatible with a uniform cofinal bound. They do not prove one. Machine-zero cancellation at sampled `k` is not a quantifier.

## FINAL PROPOSAL

Do **not** spend another kill-test on the retracted `sum |H|` growth law.

Freeze the next theorem-shaped target as:

```text
W5_SIGNED_ESTAR_L1_AND_DERIVATIVE_COFINAL_BOUND
```

Required output: source-locked constants `C_L1, C_D < infinity` and a cofinal index `k0` such that for every `k >= k0`, the exact signed production objects satisfy

\[
L1_k\le C_{L1},\qquad Derivative_k\le C_D.
\]

The jump contribution is then handled by the already proved seam decay plus exact endpoint suppliers.

The preferred representation is **not** termwise absolute summation. Preserve the signed `E_star` sum until after cancellation. Where an exact Poisson/inversion completion exists, use it before taking norms; this is the C13 pattern.

Registered prediction before proof:

```text
P_W5_SIGNED_1:
  sup_k L1_k < infinity and sup_k Derivative_k < infinity are both true
  on the exact selected family.
  confidence: 0.76

P_W5_SIGNED_2:
  any proof that applies triangle inequality across the n-sum before using
  zero mass will lose the required cofinal bound.
  confidence: 0.94
```

## STRONGEST ATTACK

Zero mass alone does **not** imply a uniform bound on

\[
\left|\sum_n H(nu)\right|.
\]

It only explains why the previous positive-term asymptotic is irrelevant and supplies a cancellation mechanism that a correct proof must exploit. The strongest remaining objection is therefore:

> the observed cancellation may be numerical and nonuniform in `u` or `k`.

A valid proof must produce a uniform signed envelope before integration. If all available estimates first replace the signed sum by `sum |H|`, the route has returned to the killed surrogate and must stop.

Two admissible re-representations if the direct signed bound stalls:

1. **Exact Poisson/inversion completion** of the signed lattice sum before norms. Kill-power 9/10, proof cost 6/10.
2. **Summation-by-parts / zero-mass discrete primitive** converting the lattice sum to differences of a decaying primitive. Kill-power 8/10, proof cost 5/10.

## CODEX DIRECTIVE

```text
NO EXECUTION DIRECTIVE FROM THIS VERDICT.

Do not rerun or formalize the retracted sum|H| growth probe.
Do not infer a cofinal theorem from the current numerical constants.
Do not move the modulus inside the E_star sum.

Next execution requires an owner-scoped theorem request for:
  W5_SIGNED_ESTAR_L1_AND_DERIVATIVE_COFINAL_BOUND
```

## META CLOSEOUT

- What became smaller? The alleged `C_k` growth wall disappeared; W5 is again two signed cofinal bounds plus the already shrinking jump ledger.
- What was killed? The surrogate `sum_n |H(nu)|` as a discriminator for W5.
- What must not be tried again? Triangle-inequality-first analysis of the `E_star` lattice sum.
- Current smallest named gap? `W5_SIGNED_ESTAR_L1_AND_DERIVATIVE_COFINAL_BOUND`.
- Next cheapest decisive test? Derive a uniform signed envelope using the exact zero-mass/inversion identity; no new large numeric sweep.
- Fate of prior prediction? `C_k ~ (k+2)^(1/4)` is **REFUTED**. `sup_k C_k < infinity unreachable` is **RETRACTED**.
- Memory entry:

```yaml
iteration:
  target: W5 cofinal packet budget
  status: PROGRESS
  failed_strategy: termwise_absolute_lattice_sum_probe
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: W5_SIGNED_ESTAR_L1_AND_DERIVATIVE_COFINAL_BOUND
  invariant_learned: zero_mass_cancellation_must_be_preserved_before_norm
  forbidden_future_move: move_modulus_inside_Estar_sum
  next_decisive_test: proof_grade_uniform_signed_envelope
```
