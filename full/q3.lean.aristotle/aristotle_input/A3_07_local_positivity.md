# A3 Local Positivity Lemma

## Goal
Prove that a Toeplitz truncation with Lipschitz symbol has a quadratic form lower bound determined by the symbol's positive floor on an arc.

## Definitions

```lean
-- Toeplitz truncation T_{P_A}^{(N)} as N×N matrix
noncomputable def ToeplitzTruncation (P_A : ℝ → ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => (1 / (2 * Real.pi)) * ∫ θ in Set.Icc 0 (2 * Real.pi),
    P_A θ * Real.cos ((i.val - j.val : ℤ) * θ)

-- Quadratic form
noncomputable def quadForm (M : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * M i j * v j

-- L² norm squared
noncomputable def l2NormSq (v : Fin N → ℝ) : ℝ := ∑ i, v i ^ 2

-- Lipschitz with constant L
def LipschitzConst (P_A : ℝ → ℝ) (L : ℝ) : Prop := ∀ x y, |P_A x - P_A y| ≤ L * |x - y|

-- Modulus of continuity
noncomputable def modCont (P_A : ℝ → ℝ) (h : ℝ) : ℝ := ⨆ (x y : ℝ), (|x - y| ≤ h) → |P_A x - P_A y|

-- Arc with positive floor
structure PosArc (P_A : ℝ → ℝ) (Γ : Set ℝ) (c₀ : ℝ) : Prop where
  is_arc : ∃ θ₀ ℓ, ℓ > 0 ∧ Γ = Set.Icc (θ₀ - ℓ/2) (θ₀ + ℓ/2)
  pos_floor : ∀ θ ∈ Γ, P_A θ ≥ c₀
  c0_pos : c₀ > 0
```

## Main Lemma to Prove

```lean
/-- Local positivity: Toeplitz quadratic form bounded below by symbol floor minus modulus loss -/
lemma local_positivity (P_A : ℝ → ℝ) (N : ℕ) (Γ : Set ℝ) (c₀ L : ℝ)
    (hLip : LipschitzConst P_A L)
    (hArc : PosArc P_A Γ c₀)
    (hN : N > 0) :
    ∃ C > 0, ∀ v : Fin N → ℝ,
      quadForm (ToeplitzTruncation P_A N) v ≥ c₀ * l2NormSq v - C * modCont P_A (1/N) * l2NormSq v := by
  sorry

/-- Corollary: For large N, quadratic form is at least c₀/2 -/
lemma local_positivity_large_N (P_A : ℝ → ℝ) (Γ : Set ℝ) (c₀ L : ℝ)
    (hLip : LipschitzConst P_A L)
    (hArc : PosArc P_A Γ c₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ v : Fin N → ℝ,
      quadForm (ToeplitzTruncation P_A N) v ≥ (c₀ / 2) * l2NormSq v := by
  sorry
```

## Proof Sketch

### For local_positivity:

1. **Trigonometric representative**: Write v as coefficients of a trig polynomial V(θ)

2. **Integral representation**:
   ⟨T_{P_A}^{(N)} v, v⟩ = (1/2π) ∫₀^{2π} P_A(θ) |V(θ)|² dθ

3. **Split the integral**:
   - Over Γ: P_A(θ) ≥ c₀, contributing ≥ c₀ · (1/2π) ∫_Γ |V|²
   - Outside Γ: Use frequency localization of v and modulus of continuity

4. **Toeplitz remainder estimate**:
   - The remainder from outside Γ is bounded by C · ω_{P_A}(1/N) · ‖v‖²
   - C depends on ‖P_A‖_∞ and Lip(P_A)

5. **Combine**: ⟨T v, v⟩ ≥ c₀ ‖v‖² - C · ω_{P_A}(1/N) · ‖v‖²

### For local_positivity_large_N:

1. Since P_A is Lipschitz: ω_{P_A}(h) ≤ L · h

2. For N large enough: C · ω_{P_A}(1/N) ≤ C · L/N ≤ c₀/2

3. Take N₀ = ⌈2CL/c₀⌉

4. Then: ⟨T v, v⟩ ≥ c₀ ‖v‖² - (c₀/2) ‖v‖² = (c₀/2) ‖v‖²

## Notes

- This lemma is used to transfer local symbol positivity to Toeplitz positivity
- The constant C is explicit and depends only on ‖P_A‖_∞ and Lip(P_A)
- In application: c₀ comes from the archimedean floor (Lemma a3-arch-floor)
- The trig polynomial representation connects finite matrices to function spaces
- Use `Matrix.PosSemidef` for the final PSD conclusion
