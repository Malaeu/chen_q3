# Spec: P_A_continuous (A3_FLOOR)

## Goal
Close the axiom in `A3_FLOOR_v22_stage4_floor.lean`:
```
theorem P_A_continuous : Continuous (P_A B_min t_sym)
```

## Definitions (in file)
```
def w (B t xi : ℝ) : ℝ :=
  max 0 (1 - |xi| / B) * Real.exp (-4 * Real.pi^2 * t * xi^2)

def g (B t xi : ℝ) : ℝ := Q3.a xi * w B t xi

def P_A (B t theta : ℝ) : ℝ :=
  2 * Real.pi * ∑' (m : ℤ), g B t (theta + m)
```
Constants: `B_min = 3`, `t_sym = 3/50`.

## Known lemmas in file
- `P_A_eq_sum6` on `Set.Icc (0) (1/2)` (finite sum of 6 g-terms).
- `P_A_even`.
- `g_even` and `w_even`.
- `continuousOn_a` in `A3_FLOOR_v19_monotonicity.lean`.
- Axiom `Q3.a_star_continuous` (if you prefer a short proof).

## Lemma chain (preferred)
1. `continuous_w`:
   ```lean
   lemma continuous_w (B t : ℝ) : Continuous (fun xi => w B t xi) := by
     -- continuity of max/abs/exp
     continuity
   ```
2. `continuous_a` (short path):
   derive from `Q3.a_star_continuous` and `Q3.a_star = 2*pi*a`.
3. `continuous_g`:
   ```lean
   lemma continuous_g (B t : ℝ) : Continuous (fun xi => g B t xi) := by
     simpa [g] using (continuous_a.mul (continuous_w B t))
   ```
4. `continuousOn_P_A_Icc0_half`:
   use `P_A_eq_sum6` to rewrite as finite sum; continuity follows from `continuous_g`.
5. Extend to `Set.Icc (-1/2) (1/2)` using `P_A_even`.
6. `P_A_periodic` (period 1) by reindexing the `tsum`.
7. Conclude `P_A_continuous` from periodicity + continuity on a fundamental domain.

## Tactic policy
- Prefer `suffices` over long `have` chains.
- Avoid `exact?` and heavy `aesop`.

## Notes
- If `tsum` reindexing is painful, you can avoid it by using the finite-sum formula
  on a fundamental domain plus a `fract`/`floor` argument to move any `theta` into it.
