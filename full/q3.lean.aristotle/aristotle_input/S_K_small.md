# S_K Small Axiom — Full Proof

## Setup

Let K ≥ 1 be a compact parameter.

### Definitions

```lean
-- Maximum node index
def N_K (K : ℝ) : ℕ := Nat.floor (Real.exp (2 * Real.pi * K))

-- Minimum node spacing
def delta_K (K : ℝ) : ℝ := 1 / (2 * Real.pi * (N_K K + 1))

-- Heat parameter minimum for contraction
def t_min (K η : ℝ) : ℝ := (delta_K K)^2 / (4 * Real.log (2/η + 1))

-- Geometric series bound
def S_K (K t : ℝ) : ℝ :=
  2 * Real.exp (-(delta_K K)^2 / (4 * t)) / (1 - Real.exp (-(delta_K K)^2 / (4 * t)))
```

## Theorem Statement

For small enough t, S_K can be made arbitrarily small:

```lean
theorem S_K_small (K t η : ℝ) (hK : K ≥ 1) (hη : η > 0) (ht : t ≤ t_min K η) :
    S_K K t ≤ η
```

## Proof

### Step 1: Express S_K in terms of r = exp(-δ²/(4t))

Let δ = delta_K K and r = exp(-δ²/(4t)).

Then:
```
S_K = 2r / (1 - r)
```

### Step 2: Bound r when t ≤ t_min

From t ≤ t_min = δ²/(4 log(2/η + 1)):
```
δ²/(4t) ≥ δ²/(4 · t_min) = log(2/η + 1)
```

Therefore:
```
r = exp(-δ²/(4t)) ≤ exp(-log(2/η + 1)) = 1/(2/η + 1) = η/(2 + η)
```

### Step 3: Bound S_K

With r ≤ η/(2 + η):
```
S_K = 2r/(1-r)
    ≤ 2 · (η/(2+η)) / (1 - η/(2+η))
    = 2 · (η/(2+η)) / ((2+η-η)/(2+η))
    = 2 · (η/(2+η)) / (2/(2+η))
    = 2 · η / 2
    = η
```

∎

## Expected Lean Proof

```lean
theorem S_K_small (K t η : ℝ) (hK : K ≥ 1) (hη : η > 0) (ht : t ≤ t_min K η) :
    S_K K t ≤ η := by
  unfold S_K t_min delta_K
  set δ := 1 / (2 * Real.pi * (↑(N_K K) + 1)) with hδ_def
  set r := Real.exp (-δ^2 / (4 * t)) with hr_def

  -- Step 1: Show r ≤ η/(2+η) from t ≤ t_min
  have h_r_bound : r ≤ η / (2 + η) := by
    rw [hr_def]
    -- From ht: t ≤ δ²/(4 log(2/η + 1))
    -- So δ²/(4t) ≥ log(2/η + 1)
    have h1 : δ^2 / (4 * t) ≥ Real.log (2/η + 1) := by
      have ht_pos : t > 0 := by
        calc t ≤ t_min K η := ht
          _ = δ^2 / (4 * Real.log (2/η + 1)) := rfl
          _ > 0 := by positivity
      calc δ^2 / (4 * t)
          ≥ δ^2 / (4 * t_min K η) := by
              apply div_le_div_of_nonneg_left (sq_nonneg δ) (by positivity)
              linarith
        _ = δ^2 / (4 * (δ^2 / (4 * Real.log (2/η + 1)))) := rfl
        _ = Real.log (2/η + 1) := by field_simp
    -- Therefore exp(-δ²/(4t)) ≤ exp(-log(2/η + 1)) = 1/(2/η + 1)
    calc r = Real.exp (-δ^2 / (4 * t)) := hr_def
      _ ≤ Real.exp (-Real.log (2/η + 1)) := Real.exp_le_exp.mpr (neg_le_neg h1)
      _ = 1 / (2/η + 1) := by rw [Real.exp_neg, Real.exp_log (by linarith)]; ring
      _ = η / (2 + η) := by field_simp; ring

  -- Step 2: Show S_K = 2r/(1-r) ≤ η
  have hr_lt_one : r < 1 := by
    calc r ≤ η / (2 + η) := h_r_bound
      _ < 1 := by
        rw [div_lt_one (by linarith)]
        linarith

  calc 2 * r / (1 - r)
      ≤ 2 * (η / (2 + η)) / (1 - η / (2 + η)) := by
          apply div_le_div
          · exact mul_le_mul_of_nonneg_left h_r_bound (by norm_num)
          · rw [sub_pos]; exact hr_lt_one
          · rw [sub_pos]; calc η / (2 + η) < 1 := by rw [div_lt_one (by linarith)]; linarith
          · apply sub_le_sub_left h_r_bound
    _ = 2 * (η / (2 + η)) / (2 / (2 + η)) := by ring_nf
    _ = η := by field_simp; ring
```

## Key Lemmas Needed

1. `Real.exp_le_exp` — monotonicity of exp
2. `Real.exp_neg` — exp(-x) = 1/exp(x)
3. `Real.exp_log` — exp(log(x)) = x for x > 0
4. `div_le_div` — division inequalities
5. `sub_le_sub_left` — subtraction monotonicity
