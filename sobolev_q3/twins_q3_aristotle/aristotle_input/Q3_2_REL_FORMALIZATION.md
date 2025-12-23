# Q3-2_rel Formalization for Lean 4

## Goal

Formalize the **relative contraction** version of Q3-2, which is numerically stable
and confirmed by tests up to N = 100,000.

---

## 1. Definitions

### 1.1 Balanced Operator (per dyadic block)

```lean
/-- Dyadic block: primes in [2^j, 2^{j+1}) -/
def DyadicBlock (j : ℕ) : Set ℕ := {p | Nat.Prime p ∧ 2^j ≤ p ∧ p < 2^(j+1)}

/-- Node map: ξ_p = log(p) / (2π) -/
noncomputable def xi (p : ℕ) : ℝ := Real.log p / (2 * Real.pi)

/-- Heat kernel Gram matrix entry -/
noncomputable def G_entry (t : ℝ) (p q : ℕ) : ℝ :=
  Real.exp (-(xi p - xi q)^2 / (4 * t))

/-- Weight function: w(p) = Λ(p) / √p -/
noncomputable def w (p : ℕ) : ℝ := (vonMangoldt p : ℝ) / Real.sqrt p

/-- Phase twist: U_α diagonal with e(α·p) -/
noncomputable def phase (α : ℝ) (p : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * α * p)

/-- Balanced operator B_{α,j} = G_j^{1/2} · W_j · U_{α,j} · G_j^{1/2} -/
-- (Matrix definition over DyadicBlock j)
```

### 1.2 Operator Norm

```lean
/-- Operator norm: ‖B‖₂ = sqrt(λ_max(B* B)) -/
noncomputable def opNorm (B : Matrix n n ℂ) : ℝ :=
  Real.sqrt (Matrix.IsHermitian.eigenvalues_max (B.conjTranspose * B))
```

---

## 2. Q3-2_rel Statement

### 2.1 Relative Contraction Ratio

```lean
/-- Relative contraction ratio -/
noncomputable def r_ratio (α : ℝ) (N j : ℕ) (t : ℝ) : ℝ :=
  opNorm (B_alpha α j t) / opNorm (B_alpha 0 j t)
```

### 2.2 Q3-2_rel Hypothesis

```lean
/-- Q3-2_rel: relative contraction on minor arcs -/
def Q3_2_rel (ρ : ℝ) (N₀ Q : ℕ) (t : ℝ) : Prop :=
  0 < ρ ∧ ρ < 1 ∧
  ∀ N ≥ N₀, ∀ α ∈ minorArcs N Q,
    ∀ j, (2^j : ℕ) ≤ N →
      r_ratio α N j t ≤ ρ
```

---

## 3. Mass Lemma

### 3.1 Statement

```lean
/-- Mass lemma: baseline product is O(N^{1/2}) -/
def MassLemma (N : ℕ) (t : ℝ) : Prop :=
  ∃ C > 0, ∀ N' ≥ N,
    let J := Nat.log2 N'
    let u_norm := sorry  -- ‖u_N‖
    let v_norm := sorry  -- ‖v_N‖
    let prod_B0 := ∏ j in Finset.range J, opNorm (B_alpha 0 j t)
    u_norm * v_norm * prod_B0 ≤ C * Real.sqrt N'
```

### 3.2 Why Mass Lemma is needed

The relative contraction Q3-2_rel gives:
```
∏ ‖B_{α,j}‖ ≤ ρ^J · ∏ ‖B_{0,j}‖
```

But to get |S(α)| ≪ N^{1/2-δ}, we need the baseline mass bounded:
```
‖u_N‖ · ‖v_N‖ · ∏ ‖B_{0,j}‖ ≪ N^{1/2}
```

---

## 4. Main Theorem: Q3-2_rel implies Q3-1

```lean
/-- From Q3-2_rel + MassLemma to Q3-1 (minor arc bound) -/
theorem Q3_2_rel_implies_Q3_1
  (ρ : ℝ) (N₀ Q : ℕ) (t : ℝ)
  (h_rel : Q3_2_rel ρ N₀ Q t)
  (h_mass : MassLemma N₀ t)
  : Q3_1 N₀ Q :=
by
  -- Let J = log₂ N
  -- |S(α)| ≤ ‖u‖ · ‖v‖ · ∏ ‖B_{α,j}‖ + Err
  --        ≤ ‖u‖ · ‖v‖ · ρ^J · ∏ ‖B_{0,j}‖ + Err    (by Q3-2_rel)
  --        ≤ C · N^{1/2} · ρ^J + Err                  (by MassLemma)
  --        = C · N^{1/2} · N^{-δ} + Err               (since ρ^J = N^{log ρ})
  --        ≪ N^{1/2 - δ'}
  sorry
```

---

## 5. Numerical Evidence

| N | r_bdry | r_rnd_max | Status |
|---|--------|-----------|--------|
| 5k | 0.437 | 0.155 | ✅ |
| 10k | 0.440 | 0.182 | ✅ |
| 50k | 0.448 | 0.044 | ✅ |
| 100k | 0.444 | 0.040 | ✅ |

**Empirical ρ ≈ 0.45 < 1** uniform across all N and all dyadic blocks.

---

## 6. Key Insight: Why NOT G^{-1}

The identity:
```
‖B_{α,j}‖² = sup_{y≠0} [y*(W U_α G U_α* W)y] / [y* G^{-1} y]
```

Is **formally correct** but **numerically fragile**:
- In upper dyadic blocks, G ≈ 1_{n×n} (all entries ≈ 1)
- cond(G) ~ 10^17 → G^{-1} gives numerical garbage
- Phases e(αp) don't affect z*Gz when G ≈ const

**Solution:** Use operator norm ratio ‖B_α‖/‖B_0‖ directly via Power Iteration.

---

## 7. Lean 4 Skeleton

```lean
import Mathlib

/-- Parameters -/
structure Q3Params where
  t : ℝ
  ht : t > 0
  Q : ℕ
  hQ : Q > 0
  ρ : ℝ
  hρ_pos : 0 < ρ
  hρ_lt1 : ρ < 1

/-- Q3-2_rel statement -/
axiom q3_2_rel (p : Q3Params) :
  ∀ N ≥ p.Q, ∀ α ∈ minorArcs N p.Q,
    ∀ j, (2^j : ℕ) ≤ N →
      opNorm (B_alpha α j p.t) ≤ p.ρ * opNorm (B_alpha 0 j p.t)

/-- Mass lemma -/
axiom mass_lemma (p : Q3Params) :
  ∃ C > 0, ∀ N ≥ p.Q,
    u_norm N * v_norm N * ∏ j in range (log2 N), opNorm (B_alpha 0 j p.t) ≤ C * sqrt N

/-- Main theorem -/
theorem q3_1_from_q3_2_rel (p : Q3Params) :
  ∀ N ≥ p.Q, ∀ α ∈ minorArcs N p.Q,
    |S_psi α N| ≤ C * N^(1/2 - δ) :=
by
  intro N hN α hα
  -- Apply Rep(N) decomposition
  -- Apply q3_2_rel to get ρ^J factor
  -- Apply mass_lemma to bound baseline
  -- Conclude with N^{1/2-δ} bound
  sorry
```

---

## 8. What Aristotle Should Produce

1. **Formalize Q3-2_rel** as a Lean 4 definition
2. **Formalize MassLemma** as a separate hypothesis
3. **Prove Q3_2_rel_implies_Q3_1** (main bridge theorem)
4. **Leave axioms for:**
   - q3_2_rel (numerical evidence ρ ≈ 0.45)
   - mass_lemma (needs separate proof)
   - Rep(N) representation formula

---

## 9. Connection to Existing Code

- **Q3_2_BRIDGE_v2.4.lean**: Contains old absolute formulation, needs update
- **boundary_alpha_stress_test_v4.py**: Numerical verification of Q3-2_rel
- **TOEPLITZ_CONTRACTION.md**: Theoretical background (Toeplitz model)
