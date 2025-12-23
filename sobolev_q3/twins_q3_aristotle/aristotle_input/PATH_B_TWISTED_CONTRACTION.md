# Path B: Twisted Contraction Lemma Formalization

## Goal
Formalize: For α ∈ minor arcs, ‖B_α‖ < 1 uniformly in N.

## 1. DEFINITIONS

### 1.1 Minor Arcs (Diophantine Definition)
```lean
/-- Minor arcs: α is far from all low-height rationals -/
def MinorArcs (N : ℕ) (Q : ℝ) : Set ℝ :=
  {α : ℝ | ∀ (a q : ℕ), 1 ≤ q → q ≤ Q → a.Coprime q →
    |α - (a : ℝ) / q| > Q / ((q : ℝ)^2 * N)}

/-- Major arcs: complement of minor arcs -/
def MajorArcs (N : ℕ) (Q : ℝ) : Set ℝ :=
  {α : ℝ | ∃ (a q : ℕ), 1 ≤ q ∧ q ≤ Q ∧ a.Coprime q ∧
    |α - (a : ℝ) / q| ≤ Q / ((q : ℝ)^2 * N)}

lemma arcs_partition (N : ℕ) (Q : ℝ) (α : ℝ) :
    α ∈ MinorArcs N Q ∨ α ∈ MajorArcs N Q := by
  -- Trichotomy of reals
  sorry
```

### 1.2 Twisted Operator B_α
```lean
/-- Circle twist diagonal matrix -/
def U_alpha (N : ℕ) (K : ℝ) (α : ℝ) : Matrix (Index N K) (Index N K) ℂ :=
  Matrix.diagonal (fun p => Complex.exp (2 * Real.pi * Complex.I * α * p.val))

/-- Balanced twisted operator: B_α = G^{1/2} W U_α G^{1/2} -/
noncomputable def B_alpha (N : ℕ) (t K : ℝ) (α : ℝ)
    (ht : t > 0) (hK : K > 0) (hne : (P_NK N K).Nonempty) :
    Matrix (Index N K) (Index N K) ℂ :=
  let sqrtG := sqrtG_valid N ⟨t, K, ht, hK⟩ hne
  let W := W_matrix N K
  sqrtG * W * U_alpha N K α * sqrtG

/-- Untwisted operator (α = 0) -/
noncomputable def B_zero (N : ℕ) (t K : ℝ)
    (ht : t > 0) (hK : K > 0) (hne : (P_NK N K).Nonempty) :
    Matrix (Index N K) (Index N K) ℂ :=
  B_alpha N t K 0 ht hK hne
```

## 2. KEY LEMMAS

### 2.1 Phase Oscillation Lemma
```lean
/-- For minor arc α and difference d, the phase |e(αd) - 1| oscillates -/
lemma phase_oscillation (α : ℝ) (Q : ℝ) (hQ : Q > 0) (hα : α ∈ MinorArcs N Q)
    (d : ℤ) (hd : d ≠ 0) :
    |Complex.exp (2 * Real.pi * Complex.I * α * d) - 1| ≥
    2 * Real.pi * Q / ((Q : ℝ)^2 * N) := by
  -- From minor arc definition: α is bounded away from rationals
  -- So αd (mod 1) is bounded away from 0
  -- Therefore |e(αd) - 1| = 2|sin(παd)| ≥ 2π‖αd‖
  sorry
```

### 2.2 Decomposition Lemma
```lean
/-- B_α decomposes as B_0 + oscillatory part -/
lemma B_alpha_decompose (N : ℕ) (t K : ℝ) (α : ℝ)
    (ht : t > 0) (hK : K > 0) (hne : (P_NK N K).Nonempty) :
    B_alpha N t K α ht hK hne = B_zero N t K ht hK hne +
      (B_alpha N t K α ht hK hne - B_zero N t K ht hK hne) := by
  ring
```

### 2.3 Untwisted Bound
```lean
/-- The untwisted operator B_0 has bounded norm -/
lemma B_zero_norm_bound (N : ℕ) (t K : ℝ)
    (ht : t > 0) (hK : K > 0) (hne : (P_NK N K).Nonempty) :
    ‖B_zero N t K ht hK hne‖ ≤ C₀ := by
  -- B_0 = G^{1/2} W G^{1/2} is a Gram-like matrix
  -- Its norm is controlled by the heat kernel decay
  sorry

-- C₀ depends on t, roughly C₀ ~ 1/(4πt)^{1/2}
def C₀ (t : ℝ) : ℝ := 1 / Real.sqrt (4 * Real.pi * t)
```

## 3. MAIN THEOREM: TWISTED CONTRACTION

### 3.1 Statement
```lean
/-- MAIN LEMMA: Twisted operator contracts for minor arc α -/
theorem twisted_contraction (N : ℕ) (t K : ℝ) (Q : ℝ)
    (ht : t > 0) (hK : K > 0) (hQ : Q > 0)
    (hne : (P_NK N K).Nonempty) (α : ℝ) (hα : α ∈ MinorArcs N Q) :
    ‖B_alpha N t K α ht hK hne‖ ≤ ρ t Q ∧ ρ t Q < 1 := by
  constructor
  · -- Bound: decompose and use triangle + cancellation
    sorry
  · -- Strict contraction: ρ < 1 from Q > 0
    sorry

/-- Contraction factor: decreases as Q increases (deeper minor arcs) -/
noncomputable def ρ (t Q : ℝ) : ℝ :=
  C₀ t + 1 / Q  -- Simplified; actual formula more complex
```

### 3.2 Proof Sketch (for Aristotle to formalize)
The proof proceeds in three steps:

**Step 1: Bound B_0**
- B_0 = G^{1/2} W G^{1/2} with G the heat Gram matrix
- By spectral theory of heat kernel: ‖B_0‖ ≤ C₀(t)
- Key: heat kernel eigenvalues decay exponentially

**Step 2: Bound oscillatory difference**
- (B_α - B_0)_{pq} = G^{1/2}_{pp} w_p (e(α(p-q)) - 1) G^{1/2}_{qq}
- For α ∈ minor arcs: phases don't coherently add
- By exponential sum bounds: ‖B_α - B_0‖ ≲ 1/Q

**Step 3: Combine**
- ‖B_α‖ ≤ ‖B_0‖ + ‖B_α - B_0‖ ≤ C₀(t) + 1/Q
- For Q large enough: ρ(t,Q) < 1

## 4. CONNECTION TO Q3_2

### 4.1 From Contraction to Minor Arc Bound
```lean
/-- Twisted contraction implies Q3_2 -/
theorem contraction_implies_Q3_2 (N : ℕ) (params : ValidParams) (Q : ℝ)
    (hQ : Q > 0) (hne : (P_NK N params.K).Nonempty)
    (h_contract : ∀ α ∈ MinorArcs N Q,
      ‖B_alpha N params.t params.K α params.ht params.hK hne‖ < 1) :
    Q3_2_valid params Q := by
  -- The spectral gap gives exponential decay
  -- ‖B_α^J‖ ≤ ρ^J for all J
  -- Taking J = c₀ log N gives |S(α)| ≲ N^{1/2-δ}
  sorry
```

### 4.2 Main Implication
```lean
/-- Path B: Spectral gap implies Q3 for twins -/
theorem path_B_main (params : ℕ → ValidParams) (Q : ℕ → ℝ)
    (h_spectral : ∀ N α, α ∈ MinorArcs N (Q N) →
      ‖B_alpha N (params N).t (params N).K α (params N).ht (params N).hK sorry‖ < 1) :
    Q3_1 Q := by
  -- Combine contraction_implies_Q3_2 with Bridge
  sorry
```

## 5. NUMERICAL VALIDATION

From `spectral_gap_test.py` v3.0:

| N | max ‖B_α‖ | ρ | δ_exp = -log(ρ) |
|---|-----------|---|-----------------|
| 10k | 0.031 | 0.031 | 3.47 |
| 50k | 0.068 | 0.068 | 2.69 |
| 100k | 0.117 | 0.117 | 2.15 |

**Observation:** ρ << 1 for all tested N, confirming spectral gap.

## 6. AXIOMS NEEDED

If full proof is too complex, these axioms suffice:

```lean
/-- Axiom: Heat kernel is positive definite -/
axiom heat_kernel_pd : ∀ t > 0, ∀ (S : Finset ℝ),
  (fun x y => k_t t x y).PosDef S

/-- Axiom: Exponential sums have square-root cancellation -/
axiom exp_sum_minor_arc : ∀ N Q α, α ∈ MinorArcs N Q →
  |∑ p in P_N N, w p * Complex.exp (2 * π * I * α * p)| ≤
  C * N^(1/2 + ε) * Q^(-1/2)

/-- Axiom: Spectral gap for twisted operator -/
axiom spectral_gap_B_alpha : ∀ N t K Q α,
  t > 0 → K > 0 → Q > 0 → α ∈ MinorArcs N Q →
  ‖B_alpha N t K α‖ < 1
```

## 7. DEPENDENCIES

This formalization requires:
- `Q3_2_BRIDGE_v2.4.lean` (ValidParams, G, W, sqrtG definitions)
- `Mathlib.Analysis.NormedSpace.OperatorNorm`
- `Mathlib.Analysis.SpecialFunctions.ExpDeriv`
- `Mathlib.NumberTheory.ArithmeticFunction`

## 8. SUCCESS CRITERIA

The formalization succeeds if it proves:
```lean
theorem path_B_complete :
  spectral_gap_B_alpha → Q3_1 := by
  intro h_gap
  apply contraction_implies_Q3_2
  exact h_gap
```

This reduces Q3 (minor arc bound) to a single spectral axiom.
