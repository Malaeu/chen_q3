# ARISTOTLE TASK A3: Sum(Q) to Rayleigh Quotient

## STATUS: New task (Block A, Step 3/3)

---

## CONTEXT

This is the **final step** connecting matrix sums to the Rayleigh quotient R(Φ_X).

**Depends on:** Task A1 (boundary row bound), Task A2 (trace/Frobenius identities)

---

## DEFINITIONS (same as Tasks A1, A2)

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

-- Gram matrix G (kernel matrix)
noncomputable def G (i j : Fin N) : ℝ := K ξ t i j

-- Matrix sums
noncomputable def SumQ : ℝ := ∑ i, ∑ j, Q ξ t i j
noncomputable def SumG : ℝ := ∑ i, ∑ j, G ξ t i j
noncomputable def TrQ : ℝ := ∑ i, Q ξ t i i
noncomputable def TrG : ℝ := ∑ i, G ξ t i i

-- Twin weights (for specific configuration)
variable (λ : Fin N → ℝ) (hλ : ∀ i, λ i ≥ 0)

-- Quadratic forms
noncomputable def E_comm (λ : Fin N → ℝ) : ℝ := ∑ i, ∑ j, λ i * λ j * Q ξ t i j
noncomputable def E_lat (λ : Fin N → ℝ) : ℝ := ∑ i, ∑ j, λ i * λ j * G ξ t i j

-- Rayleigh quotient
noncomputable def R (λ : Fin N → ℝ) : ℝ := E_comm ξ t λ / E_lat ξ t λ
```

---

## KEY INSIGHT FROM AUDIT

The paper conflates **several different ratios**:

1. **R(1)** = Sum(Q) / Sum(G) — uniform vector λ = (1,1,...,1)
2. **R(Φ_X)** — twin prime vector λ_p = Λ(p)Λ(p+2)
3. **Trace ratio** = Tr(Q) / Tr(G)
4. **Spectral ratio** = λ_max(Q) / λ_max(G)

These are **NOT the same** in general!

---

## WHAT WE CAN PROVE (rigorous)

### Lemma A3a: Uniform Vector Rayleigh

```lean
theorem R_uniform_eq_ratio :
  R ξ t (fun _ => 1) = SumQ ξ t / SumG ξ t
```

**Proof:** Direct calculation from definitions.

### Lemma A3b: Sum(Q) Structure (from A2)

```lean
-- Sum(Q) = Σ_k (row_sum_k)² where row_sum_k = Σ_j A_{kj}
theorem sumQ_as_row_sums :
  SumQ ξ t = ∑ k, (∑ j, A ξ t k j)^2
```

### Lemma A3c: Sum(G) Lower Bound

```lean
-- For positive kernel, Sum(G) ≥ N · min diagonal
theorem sumG_lower_bound :
  SumG ξ t ≥ N * (2 * Real.pi * t)
```

**Proof:** Diagonal entries G_{ii} = 2πt, and off-diagonal ≥ 0.

---

## THE HARD PART: Connecting to Growth

### What We Want (but cannot prove unconditionally)

```lean
-- CONDITIONAL: If points have "good spread", then R grows
theorem R_growth_conditional
  (h_spread : ∃ m : ℕ, ∀ k : Fin N,
    (near_points ξ (L k)).card ≥ m ∧
    ∀ j ∈ near_points ξ (L k), |ξ j - ξ k| ≥ δ) :
  R ξ t (fun _ => 1) ≥ c(t, L, δ) * m * N
```

This requires the **density hypothesis** from the audit:
- Not all points cluster at one end
- There's positive density in the "moderate zone"

---

## WHAT ARISTOTLE SHOULD PROVE

### Priority 1: Basic Identities

```lean
-- R(1) definition
theorem R_one_def :
  R ξ t (fun _ => 1) = (∑ i, ∑ j, Q ξ t i j) / (∑ i, ∑ j, G ξ t i j)

-- E_comm(1) = Sum(Q)
theorem E_comm_one :
  E_comm ξ t (fun _ => 1) = SumQ ξ t

-- E_lat(1) = Sum(G)
theorem E_lat_one :
  E_lat ξ t (fun _ => 1) = SumG ξ t
```

### Priority 2: Bounds

```lean
-- Sum(G) ≥ N · 2πt (diagonal contribution)
theorem sumG_ge_N_diag :
  SumG ξ t ≥ N * (2 * Real.pi * t)

-- For PSD Q: Sum(Q) ≥ 0
theorem sumQ_nonneg :
  SumQ ξ t ≥ 0

-- Tr(Q) ≤ Sum(Q) when all Q_{ij} ≥ 0?
-- Actually false in general! Q can have negative off-diagonal entries.
```

### Priority 3: Structure

```lean
-- Sum(Q) = ||A · 1||² (Frobenius interpretation)
theorem sumQ_as_norm :
  SumQ ξ t = ∑ k, (∑ j, A ξ t k j)^2

-- Alternative: Sum(Q) = 1ᵀ Q 1
theorem sumQ_as_quadratic :
  SumQ ξ t = E_comm ξ t (fun _ => 1)
```

---

## CONNECTION TO TWIN PRIMES

For the **twin prime application**, we use:

```
ξ_p = log(p) / (2π)    for twin prime p
λ_p = Λ(p) · Λ(p+2)    (von Mangoldt weights)

R(Φ_X) = E_comm(λ) / E_lat(λ)
```

**What we'd need to prove TPC:**
1. If #twins → ∞, then R(Φ_X) → ∞
2. Combined with SC2: finite twins ⟹ R = O(1)
3. Contradiction ⟹ infinite twins

**Gap:** Step 1 requires showing that twin distribution has enough "spread" to make Sum(Q) grow faster than Sum(G).

---

## ALTERNATIVE: Local Rayleigh Quotient

Instead of global R(Φ_X), consider **local** version:

```lean
-- Rayleigh on subset S ⊆ Fin N
noncomputable def R_local (S : Finset (Fin N)) (λ : Fin N → ℝ) : ℝ :=
  (∑ i ∈ S, ∑ j ∈ S, λ i * λ j * Q ξ t i j) /
  (∑ i ∈ S, ∑ j ∈ S, λ i * λ j * G ξ t i j)
```

**Advantage:** Can bound R_local without global density assumptions.

---

## SUCCESS CRITERIA

✓ Lemma A3a: R(1) = Sum(Q)/Sum(G)
✓ Lemma A3b: Sum(Q) structure (from A2)
✓ Lemma A3c: Sum(G) lower bound
☐ R_growth_conditional (requires density hypothesis)

---

## HINTS FOR PROOF

1. **R(1) definition:** Expand E_comm and E_lat with λ_i = 1

2. **Sum(G) bound:**
   - Diagonal: G_{ii} = 2πt
   - Off-diagonal: G_{ij} ≥ 0 (Gaussian positive)
   - Sum ≥ N · 2πt

3. **For growth results:**
   - Need to know distribution of points ξ_i
   - Use Task A1 local bounds
   - Sum over "dense" regions

---

## APPENDIX: Why This Is Hard

The fundamental difficulty:

```
Sum(Q) = Σ_k (Σ_j A_{kj})²
       = Σ_k (Σ_j (ξ_j - ξ_k) · K_{kj})²

For this to grow:
- Need pairs (k, j) where ξ_j ≠ ξ_k (so A_{kj} ≠ 0)
- Need K_{kj} not too small (so need |ξ_j - ξ_k| ≤ O(√t))
- But also need |ξ_j - ξ_k| not too small (for A_{kj} contribution)

The "sweet spot" is |ξ_j - ξ_k| ~ √t.
```

For **primes**, this sweet spot contains O(N/log N) pairs (by PNT).
For **twins**, the distribution is less understood.

This is where **Hardy-Littlewood** would help, but we're trying to avoid it!
