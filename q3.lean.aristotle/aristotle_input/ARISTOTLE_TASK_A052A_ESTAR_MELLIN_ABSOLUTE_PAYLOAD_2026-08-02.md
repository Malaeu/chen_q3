# A052A — exact absolute-dilate Mellin payload

## Goal

Produce a self-contained Lean 4 / Mathlib proof of exactly one theorem.  The
result will later be connected to a project predicate by `simpa`; do not
introduce any Q3 project imports or project-local definitions.

```lean
import Mathlib

open scoped BigOperators Topology ENNReal
open Set Filter MeasureTheory Complex

theorem eStarMellinAbsolute_payload_of_IccZero_IcoLipschitz
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal) (hb : 0 ≤ b)
    (hmeas : Measurable h)
    (hsupp : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (p : ℂ) (hp : 1 < p.re) :
    (∀ n : ℕ+,
      AEStronglyMeasurable
        (fun u : ℝ =>
          (u : ℂ) ^ (p - 1) •
            h (((n : ℕ) : ℝ) * u))
        (volume.restrict (Set.Ioi 0))) ∧
    (∑' n : ℕ+,
      ∫⁻ u : ℝ,
        ‖(u : ℂ) ^ (p - 1) •
          h (((n : ℕ) : ℝ) * u)‖ₑ
        ∂(volume.restrict (Set.Ioi 0))) ≠ ⊤ := by
  sorry
```

## Exact mathematical route

1. Derive an almost-everywhere finite uniform norm bound for `h` on its
   support.  `LipschitzOnWith` controls `Ico 0 b`; handle the single endpoint
   `b` by singleton-nullity rather than assuming continuity there.
2. Prove the `AEStronglyMeasurable` clause separately for every `n : ℕ+`.
3. In the lintegral, use the positive scaling `v = n*u`.  Bound the `n`-th
   integral by one finite constant, independent of `n`, times
   `(n : ℝ) ^ (-p.re)` (or the equivalent reciprocal form).
4. Sum the scalar majorant.  In the pinned Mathlib API the relevant p-series
   results are `Real.summable_one_div_nat_rpow` and
   `NNReal.summable_one_div_rpow`; the unqualified identifier
   `summable_one_div_rpow` is not available.
5. Transfer summability to the `ℝ≥0∞` tsum and conclude that it is not `⊤`.

An exact change-of-variables equality or a rigorous one-sided scaling bound
is acceptable.  Any bound must use an `n`-independent finite constant.

## Guardrails

- Keep the conclusion exactly in the displayed explicit predicate shape.
- Do not add a zero-mass hypothesis.
- Do not use an aggregate `Estar` square-root bound.
- Do not use zeta identities, numerical integration, fitted constants, or
  continuity of `h` at `b`.
- Do not add `axiom`, `sorry`, `admit`, `native_decide`, or `exact?` to the
  returned solution.
- Do not weaken `hp : 1 < p.re` or strengthen the support/Lipschitz class.

## Required validation

The returned file must compile with Mathlib and

```lean
#print axioms eStarMellinAbsolute_payload_of_IccZero_IcoLipschitz
```

must report only `[propext, Classical.choice, Quot.sound]` (a subset is also
acceptable).

Return the complete Lean file and one primary status:

- `ESTAR_MELLIN_ABSOLUTE_PAYLOAD_PROVED`
- `ABS_DILATE_MEASURABILITY_GAP`
- `ABS_SCALING_LINTEGRAL_GAP`
- `ABS_PSERIES_ENNREAL_GAP`
- `ABS_ENDPOINT_AE_GAP`
