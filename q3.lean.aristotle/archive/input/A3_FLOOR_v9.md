# A3_FLOOR v9: THE FINAL TWO LEMMAS

## CRITICAL INSTRUCTION

**DO NOT prove any lemmas except the TWO targets below!**

All prerequisite lemmas are ALREADY PROVEN. Use them directly as facts.

## AXIOMS (PROVEN - use directly)

```lean
-- From v3-v8, ALL these are proven:
axiom im_trigamma_neg {z : ℂ} (hz : 0 < z.re) (hzi : 0 < z.im) : (trigamma z).im < 0
axiom deriv_a_eq {ξ : ℝ} (hξ : 0 < ξ) : deriv a ξ = Real.pi * (deriv digamma (1/4 + I * Real.pi * ξ)).im
axiom continuousOn_a : ContinuousOn a (Set.Ici 0)
axiom trigamma_add_one {z : ℂ} (hz : 0 < z.re) : trigamma (z + 1) = trigamma z - 1 / z ^ 2
axiom deriv_digamma_add_one {z : ℂ} (hz : 0 < z.re) : deriv digamma (z + 1) = deriv digamma z - 1 / z ^ 2
axiom trigamma_tendsto_zero : Filter.Tendsto (fun x : ℝ => trigamma x) Filter.atTop (nhds 0)
axiom trigamma_tendsto_zero_complex {z : ℂ} (hz : 0 < z.re) : Filter.Tendsto (fun n : ℕ => trigamma (z + n)) Filter.atTop (nhds 0)
```

## KEY IDENTITY (use this!)

From the axioms, we can derive:
```
deriv digamma z = trigamma z   (for Re(z) > 0)
```

Proof sketch:
- From deriv_digamma_add_one: deriv digamma (z+n) = deriv digamma z - Σ_{k=0}^{n-1} 1/(z+k)²
- From trigamma_add_one: trigamma (z+n) = trigamma z - Σ_{k=0}^{n-1} 1/(z+k)²
- So: deriv digamma (z+n) - trigamma (z+n) = deriv digamma z - trigamma z (constant!)
- Taking limit n→∞: 0 - 0 = deriv digamma z - trigamma z
- Therefore: deriv digamma z = trigamma z

**Note on sign:** Our trigamma is Σ 1/(z+n)², which is the standard polygamma ψ₁(z).
The derivative of digamma is indeed trigamma with this definition.

## TARGET 1: deriv_a_pos

```lean
lemma deriv_a_pos {ξ : ℝ} (hξ : 0 < ξ) : deriv a ξ > 0 := by
  -- Step 1: Use deriv_a_eq
  rw [deriv_a_eq hξ]
  -- Step 2: deriv digamma = trigamma, so
  --   deriv a ξ = π * Im(trigamma (1/4 + iπξ))
  -- Step 3: For z = 1/4 + iπξ with ξ > 0:
  --   Re(z) = 1/4 > 0, Im(z) = πξ > 0
  -- Step 4: By im_trigamma_neg: Im(trigamma z) < 0
  -- Step 5: π * (negative) = negative...
  --
  -- WAIT! There's a sign issue. Let me reconsider.
  --
  -- Actually: deriv digamma = -trigamma in some conventions!
  -- Or: our im_trigamma_neg gives Im(trigamma) < 0,
  --     so Im(deriv digamma) = Im(trigamma) < 0 if they're equal,
  --     meaning π * Im(deriv digamma) = π * (negative) < 0.
  --
  -- But we want deriv a > 0!
  --
  -- Check: a(ξ) = log π - Re(digamma(1/4 + iπξ))
  -- So: a'(ξ) = -d/dξ[Re(digamma(...))]
  --           = -Re(digamma'(...) * iπ)
  --           = -Re(iπ * digamma'(...))
  --           = -π * Im(digamma'(...))  [since Re(i*w) = -Im(w)]
  --           = -π * Im(trigamma(...))
  --           = -π * (negative)         [by im_trigamma_neg]
  --           = positive!
  --
  -- So there's a SIGN in deriv_a_eq that needs checking.
  -- The axiom says: deriv a ξ = π * Im(deriv digamma ...)
  -- But the correct formula is: deriv a ξ = -π * Im(deriv digamma ...)
  --
  -- OR: deriv digamma = -trigamma (with our sign convention)
  sorry
```

**THE SIGN ISSUE:** Please verify if `deriv_a_eq` has the correct sign, then complete the proof.

## TARGET 2: strictMonoOn_a

```lean
lemma strictMonoOn_a : StrictMonoOn a (Set.Ioi 0) := by
  -- Use Convex.strictMonoOn_of_deriv_pos
  apply Convex.strictMonoOn_of_deriv_pos
  · exact convex_Ioi 0  -- Ioi 0 is convex
  · exact continuousOn_a.mono (Set.Ioi_subset_Ici le_rfl)  -- a continuous on Ioi 0
  · intro x hx
    rw [interior_Ioi]
    exact deriv_a_pos hx
  sorry
```

## EXPECTED OUTPUT

Lean 4 proofs of:
1. `deriv_a_pos` (resolving the sign issue)
2. `strictMonoOn_a`

This completes ÉTAPE 2!
