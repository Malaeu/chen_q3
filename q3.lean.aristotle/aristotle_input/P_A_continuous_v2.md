# Prove P_A_continuous

## Goal

Replace the axiom in `A3_FLOOR_v22_stage4_floor.lean` (line 23):

```lean
axiom P_A_continuous : Continuous (P_A B_min t_sym)
```

with a theorem.

## Definitions (in A3_FLOOR files)

```lean
-- A3_FLOOR_v20_bounds_core.lean
def w (B t xi : ℝ) : ℝ :=
  max 0 (1 - |xi| / B) * Real.exp (-4 * Real.pi^2 * t * xi^2)

-- A3_FLOOR_v22_stage4_floor.lean
def g (B t ξ : ℝ) : ℝ := Q3.a ξ * w B t ξ

def P_A (B t θ : ℝ) : ℝ :=
  2 * Real.pi * ∑' (m : ℤ), g B t (θ + m)
```

Constants: `B_min = 3`, `t_sym = 3/50`.

## Available axiom (USE THIS!)

From `Q3/Axioms.lean`:
```lean
axiom a_star_continuous : Continuous a_star
```

And from `Q3/Basic/Defs.lean`:
```lean
def a_star (ξ : ℝ) : ℝ := 2 * Real.pi * a ξ
```

Therefore: `a ξ = a_star ξ / (2 * Real.pi)`, so `Continuous a` follows from `a_star_continuous`.

## Available lemmas in A3_FLOOR_v22

```lean
-- Finite sum on [0, 1/2] (line 748)
lemma P_A_eq_sum6 {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
  P_A B_min t_sym θ =
    2 * Real.pi *
      (g B_min t_sym (θ - 3) + g B_min t_sym (θ - 2) + g B_min t_sym (θ - 1) +
        g B_min t_sym θ + g B_min t_sym (θ + 1) + g B_min t_sym (θ + 2))

-- Evenness
lemma P_A_even (θ : ℝ) : P_A B_min t_sym (-θ) = P_A B_min t_sym θ
```

## Proof Strategy

1. **`continuous_a`**: From `a_star_continuous` and `a = a_star / (2*pi)`:
   ```lean
   lemma continuous_a : Continuous Q3.a := by
     have h : Q3.a = fun ξ => Q3.a_star ξ / (2 * Real.pi) := by
       ext ξ; simp [Q3.a_star]; ring
     rw [h]
     exact Q3.a_star_continuous.div_const _
   ```

2. **`continuous_w`**: Composition of continuous functions (max, abs, exp, polynomial):
   ```lean
   lemma continuous_w (B t : ℝ) : Continuous (w B t) := by
     unfold w
     continuity
   ```

3. **`continuous_g`**: Product of continuous functions:
   ```lean
   lemma continuous_g (B t : ℝ) : Continuous (g B t) := by
     unfold g
     exact continuous_a.mul (continuous_w B t)
   ```

4. **`P_A_continuousOn_Icc`**: Use `P_A_eq_sum6` (finite sum of continuous → continuous):
   ```lean
   lemma P_A_continuousOn_Icc : ContinuousOn (P_A B_min t_sym) (Set.Icc 0 (1/2)) := by
     intro θ hθ
     rw [P_A_eq_sum6 hθ]
     continuity
   ```

5. **`P_A_periodic`**: Reindex the tsum:
   ```lean
   lemma P_A_periodic (θ : ℝ) : P_A B_min t_sym (θ + 1) = P_A B_min t_sym θ
   ```

6. **`P_A_continuous`**: From periodicity + continuity on fundamental domain.

## Policy

- Use `suffices` for goal reduction
- Avoid `exact?` - use explicit lemma names
- Minimize `aesop` - prefer `nlinarith`, `positivity`, `gcongr`, `continuity`
- For periodicity, the tsum reindex is standard (`Int.add_one_cast`, equiv)

## Expected output

A Lean 4 proof with NO `sorry` and NO `exact?`.
