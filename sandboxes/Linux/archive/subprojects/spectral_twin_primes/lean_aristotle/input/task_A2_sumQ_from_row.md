# ARISTOTLE TASK A2: Sum(Q) from Row Energy

## STATUS: New task (Block A, Step 2/3)

---

## CONTEXT

This is a **pure linear algebra** task. We show that the total matrix sum bounds from below by any single row.

**Depends on:** Task A1 (boundary_row_lower_bound)

---

## DEFINITIONS (same as Task A1)

```lean
variable (N : ℕ) (hN : N ≥ 2)
variable (ξ : Fin N → ℝ) (hξ : StrictMono ξ)
variable (t : ℝ) (ht : t > 0)

-- Gaussian kernel
noncomputable def K (i j : Fin N) : ℝ :=
  2 * Real.pi * t * Real.exp (-(ξ i - ξ j)^2 / (4 * t))

-- Commutator matrix A
noncomputable def A (i j : Fin N) : ℝ := (ξ j - ξ i) * K ξ t i j

-- Gram matrix Q = AᵀA
noncomputable def Q (i j : Fin N) : ℝ := ∑ k, A ξ t k i * A ξ t k j

-- Matrix sum
noncomputable def SumQ : ℝ := ∑ i, ∑ j, Q ξ t i j

-- Row norm squared (for row k)
noncomputable def row_norm_sq (k : Fin N) : ℝ := ∑ j, (A ξ t k j)^2
```

---

## LEMMA TO PROVE

### Lemma A2 (Sum(Q) ≥ Row Energy)

```lean
theorem SumQ_ge_row_sq (k : Fin N) :
  SumQ ξ t ≥ row_norm_sq ξ t k
```

**Proof sketch:**

1. By definition: Q = AᵀA, so Q_{ij} = Σ_k A_{ki} A_{kj}

2. Sum(Q) = Σᵢⱼ Qᵢⱼ = Σᵢⱼ Σₖ Aₖᵢ Aₖⱼ

3. Reorder: = Σₖ Σᵢⱼ Aₖᵢ Aₖⱼ = Σₖ (Σᵢ Aₖᵢ)²

   Wait, that's not right. Let's be more careful:

   Actually: Σᵢⱼ Qᵢⱼ = Σᵢⱼ Σₖ Aₖᵢ Aₖⱼ

   This equals: Σₖ (Σᵢ Aₖᵢ)(Σⱼ Aₖⱼ) = Σₖ (Σᵢ Aₖᵢ)²

   Hmm, but we want ≥ Σⱼ Aₖⱼ² for fixed k.

4. **Better approach:** Use Frobenius norm.

   ‖A‖_F² = Σₖⱼ Aₖⱼ² = Σₖ row_norm_sq(k)

   Also: ‖A‖_F² = Tr(AᵀA) = Tr(Q) = Σᵢ Qᵢᵢ

   So: Σᵢ Qᵢᵢ = Σₖ row_norm_sq(k)

   This means Tr(Q) = Σₖ ‖row_k‖²

5. **The actual claim:** We want Sum(Q) ≥ ‖row_k‖² for any k.

   Sum(Q) = Σᵢⱼ Qᵢⱼ

   For PSD matrix Q: Sum(Q) = 1ᵀ Q 1 ≥ 0

   Also: Sum(Q) ≥ Tr(Q) if Q has non-negative entries? Not necessarily.

6. **Direct approach:**

   Sum(Q) = Σᵢⱼ Σₖ Aₖᵢ Aₖⱼ
          = Σₖ (Σᵢ Aₖᵢ)(Σⱼ Aₖⱼ)
          = Σₖ (row_sum_k)²

   where row_sum_k = Σⱼ Aₖⱼ.

   So Sum(Q) = Σₖ (row_sum_k)².

   We want to compare this to row_norm_sq(k) = Σⱼ Aₖⱼ².

   By Cauchy-Schwarz: (Σⱼ Aₖⱼ)² ≤ N · Σⱼ Aₖⱼ²

   This goes the wrong way!

---

## REVISED LEMMA

Actually, the relationship is:

**Sum(Q) = Σₖ (row_sum_k)²** where row_sum_k = Σⱼ A_{kj}

This is NOT directly comparable to row_norm_sq = Σⱼ A_{kj}².

### Alternative: Frobenius to Trace

```lean
-- Trace of Q
noncomputable def TrQ : ℝ := ∑ i, Q ξ t i i

-- Frobenius norm of A
noncomputable def Frobenius_sq : ℝ := ∑ k, ∑ j, (A ξ t k j)^2

-- Key identity
theorem trace_eq_frobenius : TrQ ξ t = Frobenius_sq ξ t

-- Frobenius = sum of row norms
theorem frobenius_eq_rows : Frobenius_sq ξ t = ∑ k, row_norm_sq ξ t k

-- Therefore
theorem trace_ge_row (k : Fin N) : TrQ ξ t ≥ row_norm_sq ξ t k
```

---

## CORRECTED GOAL

We have two useful bounds:

### Lemma A2a: Trace(Q) = Σ_k ‖row_k(A)‖²

```lean
theorem traceQ_eq_sum_row_norms :
  TrQ ξ t = ∑ k, row_norm_sq ξ t k
```

### Lemma A2b: Trace(Q) ≥ ‖row_k(A)‖² for any k

```lean
theorem traceQ_ge_row (k : Fin N) :
  TrQ ξ t ≥ row_norm_sq ξ t k
```

### Lemma A2c: Sum(Q) and Trace relationship

For Q = AᵀA (PSD), we have:

```lean
-- Sum(Q) = ‖A · 1‖² where 1 is the all-ones vector
theorem sumQ_as_quadratic :
  SumQ ξ t = ∑ k, (∑ j, A ξ t k j)^2

-- For uniform vector λ = 1:
-- R(1) = Sum(Q) / Sum(G)
```

---

## KEY INSIGHT

The original paper's Theorem 7.3 conflates Sum(Q) with Tr(Q) or ‖A‖_F².

**Actually:**
- Tr(Q) = ‖A‖_F² = Σ_{kj} A_{kj}² (diagonal sum)
- Sum(Q) = Σᵢⱼ Qᵢⱼ = ‖A · 1‖² (quadratic form on all-ones)

For R(1) = Sum(Q)/Sum(G), we use Sum(Q), not Tr(Q).

---

## WHAT ARISTOTLE SHOULD PROVE

1. **traceQ_eq_frobenius:** Tr(Q) = ‖A‖_F²
2. **frobenius_ge_row:** ‖A‖_F² ≥ ‖row_k(A)‖² for any k
3. **sumQ_structure:** Sum(Q) = Σ_k (Σ_j A_{kj})²

These are all **pure linear algebra identities** — no number theory.

---

## SUCCESS CRITERIA

✓ Lemma A2a (trace = Frobenius)
✓ Lemma A2b (trace ≥ single row)
✓ Lemma A2c (Sum(Q) structure)
