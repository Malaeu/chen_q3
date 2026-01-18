# Prove continuity of P_A (A3_FLOOR)

Goal: replace the axiom `P_A_continuous` in `A3_FLOOR_v22_stage4_floor.lean` with a theorem.

## Target lemma

```
-- in A3_FLOOR_v22_stage4_floor.lean

theorem P_A_continuous : Continuous (P_A B_min t_sym)
```

## Definitions (already in the file)

```
def g (B t xi : ℝ) : ℝ := Q3.a xi * w B t xi

def P_A (B t θ : ℝ) : ℝ :=
  2 * Real.pi * ∑' (m : ℤ), g B t (θ + m)
```

`w` is defined in `A3_FLOOR_v20_bounds_core.lean`:

```
def w (B t xi : ℝ) : ℝ :=
  max 0 (1 - |xi| / B) * Real.exp (-4 * Real.pi^2 * t * xi^2)
```

There is already a finite-sum lemma for the A3_FLOOR parameters:

```
lemma P_A_eq_sum6 {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
  P_A B_min t_sym θ =
    2 * Real.pi *
      (g B_min t_sym (θ - 3) + g B_min t_sym (θ - 2) + g B_min t_sym (θ - 1) +
        g B_min t_sym θ + g B_min t_sym (θ + 1) + g B_min t_sym (θ + 2))
```

There is also:

```
lemma P_A_even (θ : ℝ) : P_A B_min t_sym (-θ) = P_A B_min t_sym θ
```

## Expected proof idea (sketch)

1. Show `Q3.a` is continuous using the axiom `Q3.a_star_continuous`:
   `Q3.a xi = Q3.a_star xi / (2 * Real.pi)`.
2. Show `w B_min t_sym` is continuous (max of continuous functions, abs, exp, polynomial).
3. Conclude `g B_min t_sym` is continuous as product.
4. Use `P_A_eq_sum6` to show continuity on `Icc (0, 1/2)` (finite sum of continuous terms).
5. Extend to all `θ` using periodicity of `P_A` (reindex the `tsum`) and `P_A_even` if helpful.

If needed, you may introduce helper lemmas such as:

```
lemma P_A_periodic (θ : ℝ) : P_A B_min t_sym (θ + 1) = P_A B_min t_sym θ
lemma continuous_g : Continuous (g B_min t_sym)
lemma P_A_continuousOn_Icc : ContinuousOn (P_A B_min t_sym) (Set.Icc (0:ℝ) (1/2))
```

Please provide a Lean proof with no `sorry`/`exact?`. Keep it minimal.
