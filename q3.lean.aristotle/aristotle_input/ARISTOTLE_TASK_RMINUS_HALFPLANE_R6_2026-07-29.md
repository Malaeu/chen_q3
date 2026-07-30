# R6 — close only `Rminus_differentiableOn_halfPlane`

Continue project `c746a674-5849-4dfa-9e4c-b7dd5af231b2`.

The current project has been recovered and checked locally with Lean 4.28.0 / Mathlib 4.28.0:

- `lake build` succeeds;
- exactly one forbidden hole remains:
  `RequestProject/TailAnalyticity.lean:92`;
- all other current files and the theorem `Rplus_differentiable` build.

## Sole task

Edit only `RequestProject/TailAnalyticity.lean` and replace the `sorry` in:

```lean
theorem Rminus_differentiableOn_halfPlane
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h)
    (hmass : ∫ v in Set.Ioi (0 : ℝ), h v = 0)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    DifferentiableOn ℂ (Rminus h Λ) {s : ℂ | -(1 : ℝ) / 2 < s.re} := by
  sorry
```

Do not edit `RESULT.md`, do not attempt T5, PL1–PL3, or any other theorem.

## Recommended proof route

1. Obtain the square-root bound from the already proved
   `Estar_bounded_by_sqrt_of_zeroMass`.
2. Define
   ```lean
   let f : ℝ → ℂ := Set.Ioo (0 : ℝ) (Λ⁻¹) |>.indicator (Estar h)
   ```
   and prove `Rminus h Λ = mellin f` by unfolding `Rminus` and `mellin`,
   rewriting with `integral_indicator`, and using `integral_congr_ae`.
3. Prove `LocallyIntegrableOn f (Set.Ioi 0)` from
   `Estar_locallyIntegrableOn_Ioi`, `Estar_measurable`, and indicator
   domination.
4. At `atTop`, `f` is eventually zero because it is supported in
   `(0, Λ⁻¹)`; hence it is `O(x ^ (-A))` for arbitrary `A`.
5. At `𝓝[>] 0`, use the square-root estimate on
   `0 < u < min 1 Λ⁻¹`. Convert `Real.sqrt u` with
   `Real.sqrt_eq_rpow` and prove
   ```lean
   f =O[𝓝[>] (0 : ℝ)] (fun u : ℝ => u ^ (-(-(1 : ℝ) / 2)))
   ```
   Absorb signs/nonnegativity of the existential constant into a suitable
   nonnegative constant if necessary.
6. For `s` with `-(1 : ℝ) / 2 < s.re`, rewrite by the `Rminus = mellin f`
   equality and apply
   `mellin_differentiableAt_of_isBigO_rpow`, using for example
   `a := s.re + 1` and `b := -(1 : ℝ) / 2`, then finish with
   `.differentiableWithinAt`.

## Efficiency and validation

- Work directly in the main task.
- Do not spawn subagents.
- Do not run `sleep` or polling loops.
- Do not rewrite already proved declarations.
- If one exact Mathlib statement blocks the proof after focused work, stop
  and name that statement; do not broaden the task.
- Run:
  ```bash
  lake env lean RequestProject/TailAnalyticity.lean
  rg -n "\bsorry\b|\badmit\b|\baxiom\b|native_decide|exact\?" \
    RequestProject/TailAnalyticity.lean
  ```
- Check `#print axioms
  EStarMuntzZeroMassContinuation.Rminus_differentiableOn_halfPlane`;
  permitted axioms are exactly
  `[propext, Classical.choice, Quot.sound]`.

End the response with exactly one code:

- `RMINUS_DIFFERENTIABLEON_HALFPLANE_PROVED`
- `RMINUS_SQRT_BIG_O_ASSEMBLY_GAP`
