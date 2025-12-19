# Grid-Lift Error Bound

## Goal
Prove the Grid-Lift Error Theorem: discretizing an integral over the Farey grid introduces an error controlled by the Sobolev norm of the symbol.

## Definitions

```lean
import Mathlib

open scoped BigOperators
open MeasureTheory Set Filter Topology

noncomputable section

/-- Character e(nα) = exp(2πinα) -/
noncomputable def circleChar (n : ℤ) (α : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * n * α)

/-- Fourier coefficient at frequency n -/
noncomputable def fourierCoeff (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  ∫ α in Set.Icc 0 1, f α * conj (circleChar n α)

/-- Sobolev weight (1 + |n|²)^s -/
noncomputable def sobolevWeight (s : ℝ) (n : ℤ) : ℝ :=
  (1 + (n : ℝ)^2) ^ s

/-- Sobolev norm squared: ‖f‖²_{H^s} = Σ |f̂(n)|²(1+|n|²)^s -/
noncomputable def sobolevNormSq (s : ℝ) (f : ℝ → ℂ) : ℝ :=
  ∑' n : ℤ, Complex.normSq (fourierCoeff f n) * sobolevWeight s n

/-- Sobolev norm: ‖f‖_{H^s} -/
noncomputable def sobolevNorm (s : ℝ) (f : ℝ → ℂ) : ℝ :=
  Real.sqrt (sobolevNormSq s f)

/-- f has finite Sobolev norm -/
def HasFiniteSobolevNorm (s : ℝ) (f : ℝ → ℂ) : Prop :=
  sobolevNormSq s f < ⊤

/-- Farey point a/q as real number -/
noncomputable def fareyPoint (a q : ℕ) : ℝ := (a : ℝ) / (q : ℝ)

/-- Farey grid G_M: all reduced fractions a/q with q ≤ M -/
def FareyGridReal (M : ℕ) : Finset ℝ :=
  sorry -- {a/q : a < q ≤ M, gcd(a,q) = 1}

/-- Farey arc I_γ centered at grid point γ -/
def FareyArc (M : ℕ) (γ : ℝ) : Set ℝ :=
  sorry -- mediant-based partition

/-- Farey arcs partition [0,1) -/
axiom fareyArcs_partition (M : ℕ) :
  (⋃ γ ∈ FareyGridReal M, FareyArc M γ) = Set.Ico 0 1

/-- Maximum Farey arc length is O(1/M²) -/
axiom fareyArc_length_bound (M : ℕ) (hM : M > 0) (γ : ℝ) (hγ : γ ∈ FareyGridReal M) :
  MeasureTheory.volume (FareyArc M γ) ≤ 2 / (M : ℝ)^2
```

## Main Theorem to Prove

```lean
/-- THE GRID-LIFT ERROR THEOREM

When Ψ lies in the Sobolev space H^s with s > 1/2, the discretization
error from replacing an integral by a Farey grid sum is:

  |∫_𝕋 Ψ(α)·g(α) dα - Σ_{γ∈G_M} |I_γ|·Ψ(γ)·g(γ)| ≤ C·M^{-(s-1/2)}·‖Ψ‖_{H^s}·‖g‖_∞

This is the KEY place where Sobolev regularity s > 1/2 is used.
The Sobolev embedding H^s ↪ C^{0,s-1/2} controls oscillation on each arc.
-/
theorem grid_lift_error {s : ℝ} (hs : s > 1/2) (Ψ : ℝ → ℂ)
    (hΨ : HasFiniteSobolevNorm s Ψ)
    (g : ℝ → ℝ) (hg : BddAbove (Set.range (fun x ↦ |g x|)))
    (M : ℕ) (hM : M > 0) :
    ∃ C > 0, Complex.abs (
      ∫ α in Set.Icc 0 1, Ψ α * g α -
      ∑ γ ∈ FareyGridReal M, (MeasureTheory.volume (FareyArc M γ)).toReal * Ψ γ * g γ
    ) ≤ C * (M : ℝ)^(-(s - 1/2)) * sobolevNorm s Ψ * sSup (Set.range (fun x ↦ |g x|)) := by
  sorry
```

## Proof Sketch

### Step 1: Partition into Farey arcs

By the partition property, we can write:
$$\int_0^1 \Psi(\alpha) g(\alpha) \, d\alpha = \sum_{\gamma \in G_M} \int_{I_\gamma} \Psi(\alpha) g(\alpha) \, d\alpha$$

### Step 2: Local approximation on each arc

On each Farey arc $I_\gamma$:
$$\int_{I_\gamma} \Psi(\alpha) g(\alpha) \, d\alpha = \Psi(\gamma) g(\gamma) |I_\gamma| + \text{error}_\gamma$$

where the error is bounded by the oscillation of $\Psi$ on $I_\gamma$:
$$|\text{error}_\gamma| \leq |I_\gamma| \cdot \sup_{\alpha \in I_\gamma} |\Psi(\alpha) - \Psi(\gamma)| \cdot \|g\|_\infty$$

### Step 3: Apply Sobolev embedding

By the Sobolev embedding theorem for $s > 1/2$:
$$|\Psi(\alpha) - \Psi(\gamma)| \leq C_s \|\Psi\|_{H^s} |\alpha - \gamma|^{s-1/2}$$

Since $\alpha \in I_\gamma$, we have $|\alpha - \gamma| \leq |I_\gamma| \leq C/M^2$.

Therefore:
$$\sup_{\alpha \in I_\gamma} |\Psi(\alpha) - \Psi(\gamma)| \leq C_s \|\Psi\|_{H^s} |I_\gamma|^{s-1/2}$$

### Step 4: Sum the errors

$$|\text{error}_\gamma| \leq C |I_\gamma|^{s+1/2} \cdot \|\Psi\|_{H^s} \cdot \|g\|_\infty$$

Total error:
$$\sum_\gamma |\text{error}_\gamma| \leq C \|\Psi\|_{H^s} \|g\|_\infty \sum_\gamma |I_\gamma|^{s+1/2}$$

### Step 5: Bound the sum of arc lengths

Since $|I_\gamma| \leq C/M^2$ and $\sum_\gamma |I_\gamma| = 1$:
$$\sum_\gamma |I_\gamma|^{s+1/2} \leq (\max_\gamma |I_\gamma|)^{s-1/2} \cdot \sum_\gamma |I_\gamma|$$
$$\leq (C/M^2)^{s-1/2} \cdot 1 = C' \cdot M^{-2(s-1/2)} = C' \cdot M^{-(2s-1)}$$

Wait, this gives $M^{-(2s-1)}$ not $M^{-(s-1/2)}$. Let me recalculate.

Actually for $s > 1/2$, $2s - 1 > 0$, so the error is $O(M^{-(2s-1)})$.

But the theorem statement uses $M^{-(s-1/2)}$. Let me verify:
- $2s - 1 = 2(s - 1/2)$
- So $M^{-(2s-1)} = M^{-2(s-1/2)}$ which is BETTER than $M^{-(s-1/2)}$.

The theorem is stated with the weaker bound $M^{-(s-1/2)}$ which is certainly implied.

### Step 6: Conclusion

$$\left|\int \Psi g - \sum_\gamma |I_\gamma| \Psi(\gamma) g(\gamma)\right| \leq C \cdot M^{-(s-1/2)} \cdot \|\Psi\|_{H^s} \cdot \|g\|_\infty$$

## Notes

- The key is `sobolev_embedding`: H^s ↪ C^{0,s-1/2} for s > 1/2
- Farey arcs have max length O(1/M²), which is crucial
- The partition property allows decomposing the integral
- Error control uses Hölder continuity from Sobolev embedding
- This theorem bridges continuous integrals to discrete computation
- In the Master Inequality, g = |S|² with ‖g‖_∞ ≤ X
- Typical choice: M = X^θ makes the error o(X)
- Use `MeasureTheory.integral_union` for partitioning
- Use `Set.sum_card_inter` for counting arguments
