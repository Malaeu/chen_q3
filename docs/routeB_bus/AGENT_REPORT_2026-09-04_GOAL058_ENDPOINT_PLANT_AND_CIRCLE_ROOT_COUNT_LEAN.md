# AGENT REPORT — GOAL058: P59 endpoint kill plant + polynomial circle root count (Lean)

```yaml
DATE: 2026-09-04
BOUNDARY_ID: GOAL058_WINDING_LOCK_RECTANGLE_RESULTS_AND_ENDPOINT_ATOM
SOURCE_VERDICT: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_WINDING_LOCK_RECTANGLE_RESULTS_AND_ENDPOINT_ATOM_2026-09-04.md
REPO_HEAD_AT_WORK: 8a2790340812865da80e704177220a45d88c06b1
BRANCH: rh_clean
MATHLIB: v4.26.0 (pinned, lake-manifest.json)
TOOLCHAIN: leanprover/lean4:v4.26.0

PART_A: P59_SINGLE_ENDPOINT_ATOM_COUNTEREXAMPLE_KERNEL_GREEN
PART_B: POLYNOMIAL_CIRCLE_ROOT_COUNT_KERNEL_GREEN   # complete, no missing lemma
LEAN_EDIT_PERFORMED: true   # two NEW files only, nothing existing edited
COMMIT_PERFORMED: false
NUMERICAL_RUN_PERFORMED: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## Part A — the kill plant

File: `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/P59SingleEndpointAtomCounterexample.lean`
(247 lines, new, untracked)

Namespace `Q3.RouteB.P59SingleEndpointAtom`. Objects:

```lean
def plant (a b : ℝ) : ℂ → ℂ :=
  fun z => (1 - z ^ 2 / (a : ℂ) ^ 2) * (1 - z ^ 2 / (b : ℂ) ^ 2)

def target : ℂ → ℂ := fun _ => 1
```

Directive items (`CODEX DIRECTIVE`, `THEOREM SHAPE`), all proved:

| Directive item | Theorem |
|---|---|
| `p(0) = 1` | `plant_zero`, `plant_anchor_eq_target` |
| `p(R) = 1` | `plant_at_endpoint` (hypotheses `a ≠ 0`, `b ≠ 0`, `a² + b² = R²`) |
| `e(R) = 0` | `plant_endpoint_error_eq_zero` : `‖plant a b R - target R‖ / ‖target R‖ = 0` |
| `p(±a) = 0` | `plant_at_a`, `plant_at_neg_a` |
| `p(±b) = 0` | `plant_at_b`, `plant_at_neg_b` |
| `0 < b < R` for `b = √(R² − a²)` | `sqrt_leg_spec` (also gives `a² + b² = R²`) |
| evenness of the plant | `plant_even` |
| target zero-free | `target_no_zeros` |

`sqrt_leg_pythagorean` closes the gap between the verdict's parametrisation
`b = √(R² − a²)` and the concrete instantiation used below:
`Real.sqrt (R² − (3R/5)²) = 4R/5`. The instantiation is the `3-4-5` triple, so
the counterexample needs no square-root arithmetic in the kernel and the four
roots are automatically distinct.

Packaged conclusions (the two theorems the judge asked to be explicit):

```lean
theorem single_endpoint_atom_counterexample {R : ℝ} (hR : 0 < R) :
    ∃ (F X : ℂ → ℂ) (S : Finset ℝ),
      F 0 = X 0 ∧
      F (R : ℂ) = X (R : ℂ) ∧
      ‖F (R : ℂ) - X (R : ℂ)‖ / ‖X (R : ℂ)‖ = 0 ∧
      (∀ z : ℂ, X z ≠ 0) ∧
      4 ≤ S.card ∧
      (∀ x ∈ S, F (x : ℂ) = 0 ∧ |x| < R)

theorem endpoint_agreement_does_not_control_zero_count {R : ℝ} (hR : 0 < R) :
    ¬ ∀ F X : ℂ → ℂ,
        F 0 = X 0 →
        F (R : ℂ) = X (R : ℂ) →
        (∀ z : ℂ, X z ≠ 0) →
        ∀ x : ℝ, |x| < R → F (x : ℂ) ≠ 0
```

The first exhibits the plant: anchor agreement, endpoint agreement with
`e(R) = 0`, a zero-free target, and a `Finset ℝ` of at least four distinct real
roots of `F` of absolute value `< R` (`card_four_roots` proves the card is
exactly `4`). The second is the refutation of the implication the atom
asserted: no theorem can deduce "the approximant is zero-free where the target
is", a fortiori equal zero counts, from anchor plus endpoint agreement.

Supporting: `real_mem_thin_rectangle` — a real point with `|x| < R` has
`re ∈ Ioo (-R) R` and `im ∈ Ioo (-h) h` for every `h > 0`, i.e. all four roots
sit inside every thin rectangle, which is the verdict's `divisor_difference`.

Scope discipline honoured: no general Rouché, no argument principle, no
`centeredXi`, no numerics, no `sorry`/`admit`, no new axioms, no weakening.

## Part B — polynomial circle argument principle

File: `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/PolynomialCircleRootCount.lean`
(259 lines, new, untracked)

Namespace `Q3.RouteB.PolynomialCircleRootCount`. **Complete — no missing
lemma, nothing left partial.**

```lean
theorem circleIntegral_logDeriv_eq_root_count {p : Polynomial ℂ} (hp : p ≠ 0) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hcirc : ∀ z ∈ Metric.sphere c r, p.eval z ≠ 0) :
    (∮ z in C(c, r), (Polynomial.derivative p).eval z / p.eval z)
      = 2 * (Real.pi : ℂ) * Complex.I *
          ((p.roots.filter (fun a => dist a c < r)).card : ℂ)
```

Roots are counted with multiplicity because `p.roots` is the root *multiset*.
The boundary guard is `hcirc` (no root on the circle). Corollary
`circleIntegral_logDeriv_eq_zero_of_no_root`: the integral vanishes when every
root is strictly outside the closed disk.

Chain of the four supporting theorems:

1. `differentiable_linear_prod` / `linear_prod_ne_zero` — the linear-factor
   product `∏_{a ∈ t} (z − a)` over a multiset is entire and nonzero off the
   nodes (`Multiset.induction_on`).
2. `logDeriv_linear_prod` — `logDeriv (∏ (w − a)) z = ∑ (z − a)⁻¹`.
3. `logDeriv_polynomial_eq_sum` — `p'(z)/p(z) = ∑_{a ∈ p.roots} (z − a)⁻¹`
   off the roots.
4. `circleIntegrable_inv_sum` + `circleIntegral_inv_sum` — integrability and
   term-by-term evaluation of the circle integral of the pole sum.

### Mathlib ingredients actually used (judge's list, checked against v4.26.0)

| Judge's name | Status in the pinned Mathlib | Used as |
|---|---|---|
| `Polynomial.Splits.eval_eq_prod_roots` | exists, `Mathlib/Algebra/Polynomial/Factors.lean:285`, signature `(hf : Splits f) (x) : f.eval x = f.leadingCoeff * (f.roots.map (x - ·)).prod` | factorisation |
| `Polynomial.Splits` for `ℂ` | `IsAlgClosed.splits p` (class field, `Mathlib/FieldTheory/IsAlgClosed/Basic.lean:64`) | `hsplits` |
| `logDeriv_const_mul` | exists, `Mathlib/Analysis/Calculus/LogDeriv.lean:66` | strips `leadingCoeff` |
| `logDeriv_prod` | exists (`LogDeriv.lean:71`) but is a **`Finset`** product; the root object is a `Multiset` | **not used**; replaced by `logDeriv_mul` (`LogDeriv.lean:52`) under `Multiset.induction_on`, which is exactly how `logDeriv_prod` is itself proved |
| `circleIntegral.integral_sub_inv_of_mem_ball` | exists, `Mathlib/MeasureTheory/Integral/CircleIntegral.lean:621` | inside nodes → `2πi` |
| `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable` | exists, `Mathlib/Analysis/Complex/CauchyIntegral.lean:441` | outside nodes → `0` |
| finite-sum linearity of `circleIntegral` | **no `circleIntegral.integral_finset_sum` / `integral_multiset_sum` exists** | built here from `circleIntegral.integral_add` (`CircleIntegral.lean:380`) + `circleIntegrable_sub_inv_iff` (`:329`) + `circleIntegrable_const`, by multiset induction (`circleIntegrable_inv_sum`) |
| `circleIntegral.integral_congr` (`:354`) | exists | transports `p'/p = ∑ (z−a)⁻¹` from the circle to the integral |

Two deviations from the judge's exact ingredient list, both upward-compatible:
the `Finset`-indexed `logDeriv_prod` and a nonexistent circle-integral
finite-sum lemma were replaced by multiset inductions over `logDeriv_mul` and
`circleIntegral.integral_add`. No lemma was guessed: every name above was
located by grep in `q3.lean.aristotle/.lake/packages/mathlib`.

Also confirmed by inspection, consistent with the verdict's `NEW_ANALYTIC`
classification: the pinned Mathlib has
`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`
(rectangle Cauchy–Goursat for a pole-free integrand) and **no** rectangle
argument principle, index/winding theorem, or Rouché theorem. The rectangle
layer remains open.

## Commands and exit codes

All from the working tree above, `${PIPESTATUS[0]}` captured.

```text
# WORKDIR q3.lean.aristotle
lake env lean Q3/Proofs/RouteB/P59SingleEndpointAtomCounterexample.lean          exit 0
lake build Q3.Proofs.RouteB.P59SingleEndpointAtomCounterexample                  exit 0   (7743/7743 jobs)
lake env lean Q3/Proofs/RouteB/PolynomialCircleRootCount.lean                    exit 0
lake build Q3.Proofs.RouteB.PolynomialCircleRootCount                            exit 0   (7743/7743 jobs)

# WORKDIR repo root
scripts/q3_check.sh Q3/Proofs/RouteB/P59SingleEndpointAtomCounterexample.lean \
                    Q3/Proofs/RouteB/PolynomialCircleRootCount.lean             exit 0   ("q3_check ok")
```

No `sorry`, no `admit`, no `exact?`, no new `axiom` (the `q3_check.sh` scan
covers all four).

## Axioms

`#print axioms` is kept in both files (project style). Every listed theorem
reports exactly `[propext, Classical.choice, Quot.sound]`:

```text
Q3.RouteB.P59SingleEndpointAtom.plant_at_endpoint
Q3.RouteB.P59SingleEndpointAtom.plant_endpoint_error_eq_zero
Q3.RouteB.P59SingleEndpointAtom.sqrt_leg_spec
Q3.RouteB.P59SingleEndpointAtom.card_four_roots
Q3.RouteB.P59SingleEndpointAtom.single_endpoint_atom_counterexample
Q3.RouteB.P59SingleEndpointAtom.endpoint_agreement_does_not_control_zero_count

Q3.RouteB.PolynomialCircleRootCount.logDeriv_linear_prod
Q3.RouteB.PolynomialCircleRootCount.logDeriv_polynomial_eq_sum
Q3.RouteB.PolynomialCircleRootCount.circleIntegral_inv_sub_of_outside
Q3.RouteB.PolynomialCircleRootCount.circleIntegral_inv_sum
Q3.RouteB.PolynomialCircleRootCount.circleIntegral_logDeriv_eq_root_count
Q3.RouteB.PolynomialCircleRootCount.circleIntegral_logDeriv_eq_zero_of_no_root
```

## CLOSES / OPENS

```yaml
CLOSES:
  - SINGLE_ENDPOINT_ATOM_AS_RECTANGLE_COUNT_CERTIFICATE   # kernel-checked counterexample
  - R2_POLYNOMIAL_CIRCLE_ROOT_COUNT                       # circle-only count tool now on the shelf
OPENS: []
STILL_OPEN_FROM_VERDICT:
  - P59_GROUND_XI_FULL_THIN_RECTANGLE_BOUNDARY_MARGIN     # NEW_ANALYTIC, untouched here
  - rectangle argument principle / Rouché in Lean          # absent from pinned Mathlib
```

Nothing was committed or pushed; no existing file was edited. The two new files
are untracked in the working tree.
