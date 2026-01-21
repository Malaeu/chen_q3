# ARISTOTLE TASK A1: Boundary Row Lower Bound

## STATUS: New task (Block A, Step 1/3)

---

## CONTEXT

This is a **pure linear algebra / geometry** task. No number theory.

We study the **commutator matrix** A for N points on the real line with Gaussian kernel.

---

## DEFINITIONS

```lean
-- N points on the real line, strictly increasing
variable (N : ℕ) (hN : N ≥ 2)
variable (ξ : Fin N → ℝ) (hξ : StrictMono ξ)

-- Kernel parameter
variable (t : ℝ) (ht : t > 0)

-- Gaussian kernel
noncomputable def K (i j : Fin N) : ℝ :=
  2 * Real.pi * t * Real.exp (-(ξ i - ξ j)^2 / (4 * t))

-- Commutator matrix
noncomputable def A (i j : Fin N) : ℝ := (ξ j - ξ i) * K ξ t i j

-- Boundary row (first row of A)
noncomputable def row₀ : Fin N → ℝ := fun j => A ξ t 0 j

-- Row norm squared
noncomputable def row₀_norm_sq : ℝ := ∑ j, (row₀ ξ t j)^2

-- Span
noncomputable def span : ℝ := ξ ⟨N-1, by omega⟩ - ξ 0
```

---

## GOAL

Prove a **lower bound** on the boundary row energy in terms of:
- Number of points N
- The span (ξ_{N-1} - ξ_0)
- Kernel parameter t

**Key insight:** Unlike the broken "Sum(Q) ~ N² span²" claim, we need a bound that **explicitly depends on how K decays**.

---

## LEMMA TO PROVE

### Lemma A1 (Boundary Row Lower Bound)

For the **truncated sum** over points within distance L from ξ_0:

```lean
-- Points within distance L of ξ_0
def near_points (L : ℝ) : Finset (Fin N) :=
  (Finset.univ).filter (fun j => |ξ j - ξ 0| ≤ L)

-- Truncated row energy
noncomputable def row₀_near_sq (L : ℝ) : ℝ :=
  ∑ j ∈ near_points ξ L, (row₀ ξ t j)^2

-- Lower bound on truncated energy
theorem boundary_row_lower_bound (L : ℝ) (hL : L > 0) :
  row₀_near_sq ξ t L ≥
    (2 * Real.pi * t)^2 * Real.exp(-L^2 / (2*t)) *
    ∑ j ∈ near_points ξ L, (ξ j - ξ 0)^2
```

**Proof idea:**
1. For j ∈ near_points: |ξ j - ξ 0| ≤ L
2. Therefore K(0,j) = 2πt · exp(-(ξ j - ξ 0)²/(4t)) ≥ 2πt · exp(-L²/(4t))
3. A(0,j) = (ξ j - ξ 0) · K(0,j) ≥ (ξ j - ξ 0) · 2πt · exp(-L²/(4t))
4. Square and sum: row₀_near_sq ≥ (2πt)² exp(-L²/(2t)) · Σ(ξ j - ξ 0)²

---

## COROLLARY (Counting Version)

If at least m points satisfy ξ j - ξ 0 ≥ δ for some δ > 0, then:

```lean
theorem boundary_row_counting (L δ : ℝ) (hL : L > 0) (hδ : 0 < δ) (hδL : δ ≤ L)
  (m : ℕ) (hm : (near_points ξ L).card ≥ m)
  (h_spread : ∀ j ∈ near_points ξ L, ξ j - ξ 0 ≥ δ) :
  row₀_near_sq ξ t L ≥
    (2 * Real.pi * t)^2 * Real.exp(-L^2 / (2*t)) * m * δ^2
```

---

## WHY THIS IS THE RIGHT FORMULATION

The broken Theorem 7.3 claimed "Sum(Q) ~ c(t) N² span²" with c independent of span.

**Problem:** As span → ∞ with fixed t, all K(i,j) → 0, so Sum(Q) → 0.

**Solution (this lemma):**
- We bound energy **locally** within distance L
- The constant **explicitly depends on L and t** via exp(-L²/(2t))
- No fake "universal" claim

To get global growth, we'll need to either:
1. Let t = t(N) grow with N (adaptive kernel), or
2. Show that enough points stay within "moderate" distance L

---

## HINTS FOR PROOF

1. **Expand A(0,j)²:**
   A(0,j)² = (ξ j - ξ 0)² · K(0,j)²

2. **Lower bound K(0,j)² for j ∈ near_points:**
   K(0,j)² ≥ (2πt)² exp(-L²/(2t))

   Because |ξ j - ξ 0| ≤ L implies:
   exp(-(ξ j - ξ 0)²/(4t)) ≥ exp(-L²/(4t))

   Squaring: exp(-(ξ j - ξ 0)²/(2t)) ≥ exp(-L²/(2t))

3. **Sum over near_points:**
   row₀_near_sq = Σ A(0,j)²
                ≥ Σ (ξ j - ξ 0)² · (2πt)² exp(-L²/(2t))
                = (2πt)² exp(-L²/(2t)) · Σ (ξ j - ξ 0)²

---

## SUCCESS CRITERIA

✓ Main lemma `boundary_row_lower_bound` proven
✓ Corollary `boundary_row_counting` proven

This will be used in Task A2 to bound Sum(Q).
