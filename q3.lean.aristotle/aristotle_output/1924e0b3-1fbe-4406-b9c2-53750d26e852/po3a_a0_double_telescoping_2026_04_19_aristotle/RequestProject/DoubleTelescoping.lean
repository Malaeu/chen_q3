import Mathlib

open scoped BigOperators

/-! # PO3a-A0 — Double Telescoping Extraction

A clean abstract theorem: a two-variable function `D : ℕ → ℕ → A` over an
additive commutative group decomposes as

  D m n = corner + row-strip + column-strip + bulk

where
- corner   = D 0 0
- row-strip = ∑ r < m, (D (r+1) 0 - D r 0)
- col-strip = ∑ s < n, (D 0 (s+1) - D 0 s)
- bulk      = ∑ r < m, ∑ s < n, (D (r+1)(s+1) - D (r+1) s - D r (s+1) + D r s)
-/

/-- Single-variable telescoping: `f n = f 0 + ∑ i ∈ range n, (f (i+1) - f i)`. -/
lemma single_telescoping {A : Type*} [AddCommGroup A] (f : ℕ → A) (n : ℕ) :
    f n = f 0 + ∑ i ∈ Finset.range n, (f (i + 1) - f i) := by
  induction' n with n ih;
  · simp +decide;
  · rw [ Finset.sum_range_succ, ← add_assoc, ← ih, add_sub_cancel ]

/-- **Double telescoping identity (zero-based).**

Every function `D : ℕ → ℕ → A` satisfies the decomposition into corner,
row-strip, column-strip, and bulk mixed-difference terms. -/
theorem po3_double_telescoping_zero_based
    {A : Type*} [AddCommGroup A]
    (D : ℕ → ℕ → A) (m n : ℕ) :
    D m n =
      D 0 0
        + ∑ r ∈ Finset.range m, (D (r + 1) 0 - D r 0)
        + ∑ s ∈ Finset.range n, (D 0 (s + 1) - D 0 s)
        + ∑ r ∈ Finset.range m,
            ∑ s ∈ Finset.range n,
              (D (r + 1) (s + 1) - D (r + 1) s - D r (s + 1) + D r s) := by
  induction' m with m ih generalizing n <;> simp_all +decide [ Finset.sum_range_succ ] ; abel_nf at *;
  · induction n <;> simp_all +decide [ Finset.sum_range_succ ] ; abel_nf at *;
  · induction' n with n ih' <;> simp_all +decide [ Finset.sum_range_succ ];
    · abel1;
    · simp +decide [ Finset.sum_add_distrib, Finset.sum_sub_distrib ] ; abel_nf

/-- **Double telescoping identity (shifted).**

Shifted version where the corner is at `(N+1, N+1)`. -/
theorem po3_double_telescoping_shifted
    {A : Type*} [AddCommGroup A]
    (D : ℕ → ℕ → A) (N m n : ℕ) :
    D (m + N + 1) (n + N + 1) =
      D (N + 1) (N + 1)
        + ∑ r ∈ Finset.range m, (D (r + N + 2) (N + 1) - D (r + N + 1) (N + 1))
        + ∑ s ∈ Finset.range n, (D (N + 1) (s + N + 2) - D (N + 1) (s + N + 1))
        + ∑ r ∈ Finset.range m,
            ∑ s ∈ Finset.range n,
              (D (r + N + 2) (s + N + 2) - D (r + N + 2) (s + N + 1)
               - D (r + N + 1) (s + N + 2) + D (r + N + 1) (s + N + 1)) := by
  convert po3_double_telescoping_zero_based ( fun r s => D ( r + N + 1 ) ( s + N + 1 ) ) m n using 1;
  grind