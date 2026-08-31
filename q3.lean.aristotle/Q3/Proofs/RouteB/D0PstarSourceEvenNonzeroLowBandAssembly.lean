import Q3.Proofs.RouteB.D0PstarSourceEvenNonzeroTailCarrier

set_option linter.mathlibStandardSet false

noncomputable section

open Complex MeasureTheory
open scoped ComplexConjugate NNReal

namespace Q3.RouteB.D0Pstar

/-!
# Source-Weil nonzero-even low-band assembly

This file closes the local synthesis pre-gate immediately downstream of the
source-even nonzero-tail carrier.  It proves that the normalized ambient
nonzero-even modes form an orthonormal family, assembles the finite low band
and the zero-plus-low-band head, and proves exact ambient orthogonality of that
head to the closed nonzero-even tail.

This is deliberately not a graph-inner-product orthonormality theorem, an
exhaustive even-sector direct sum, selected-row compatibility, a selected
Rayleigh-shift floor, a positive Schur margin, G1, G3, or an RH claim.  Its next
consumer is the exact selected-row/head-tail coercivity or Feshbach gate.
-/

/-- The ambient images of the normalized nonzero-even graph modes form an
orthonormal family. -/
theorem sourceWeilGraphAmbient_evenNonzeroMode_orthonormal
    (i : PairIndex) :
    Orthonormal ℂ
      (fun n : ℕ =>
        sourceWeilGraphAmbient i (sourceWeilGraphEvenNonzeroMode i n)) := by
  rw [orthonormal_iff_ite]
  intro n m
  rw [sourceWeilGraphAmbient_evenNonzeroMode,
    sourceWeilGraphAmbient_evenNonzeroMode]
  simp only [inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right]
  have hbase := orthonormal_iff_ite.mp (V_n_m_orthonormal i)
  rw [hbase, hbase, hbase, hbase]
  by_cases hnm : n = m
  · subst m
    have hcross₁ :
        (-1 + -((n : ℕ) : ℤ)) ≠ ((n : ℕ) : ℤ) + 1 := by
      omega
    have hcross₂ :
        ((n : ℕ) : ℤ) + 1 ≠ -1 + -((n : ℕ) : ℤ) := by
      omega
    simp [hcross₁, hcross₂]
    have hsqrt_ne : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.2 (by norm_num : (0 : ℝ) < 2))
    field_simp [hsqrt_ne]
    have hsqrt_sq : (((Real.sqrt 2 : ℝ) : ℂ)) ^ 2 = 2 := by
      exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
    norm_num [hsqrt_sq]
  · have hsame₁ :
        (((n : ℕ) : ℤ) + 1 = ((m : ℕ) : ℤ) + 1) ↔ n = m := by
      omega
    have hsame₂ :
        (-1 + -((n : ℕ) : ℤ) = -1 + -((m : ℕ) : ℤ)) ↔ n = m := by
      omega
    have hcross₁ :
        -1 + -((n : ℕ) : ℤ) ≠ ((m : ℕ) : ℤ) + 1 := by
      omega
    have hcross₂ :
        ((n : ℕ) : ℤ) + 1 ≠ -1 + -((m : ℕ) : ℤ) := by
      omega
    simp [hsame₁, hsame₂, hcross₁, hcross₂, hnm]

/-- Finite synthesis of the first `R` normalized nonzero-even modes. -/
noncomputable def sourceWeilGraphEvenNonzeroLowBandSynthesis
    (i : PairIndex) {R : ℕ} (c : Fin R → ℂ) :
    SourceWeilGraphCarrier i :=
  ∑ n : Fin R, c n • sourceWeilGraphEvenNonzeroMode i n.val

/-- The source-even head: zero mode plus the first `R` nonzero-even modes. -/
noncomputable def sourceWeilGraphEvenHeadSynthesis
    (i : PairIndex) {R : ℕ} (c0 : ℂ) (c : Fin R → ℂ) :
    SourceWeilGraphCarrier i :=
  c0 • sourceWeilGraphEvenZeroMode i +
    sourceWeilGraphEvenNonzeroLowBandSynthesis i c

@[simp] theorem sourceWeilGraphAmbient_evenNonzeroLowBandSynthesis
    (i : PairIndex) {R : ℕ} (c : Fin R → ℂ) :
    sourceWeilGraphAmbient i
        (sourceWeilGraphEvenNonzeroLowBandSynthesis i c) =
      ∑ n : Fin R, c n •
        (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ •
          (V_n_m i (n.val + 1 : ℕ) +
            V_n_m i (-((n.val + 1 : ℕ) : ℤ)))) := by
  unfold sourceWeilGraphEvenNonzeroLowBandSynthesis
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_smul, sourceWeilGraphAmbient_evenNonzeroMode]

@[simp] theorem sourceWeilGraphAmbient_evenHeadSynthesis
    (i : PairIndex) {R : ℕ} (c0 : ℂ) (c : Fin R → ℂ) :
    sourceWeilGraphAmbient i
        (sourceWeilGraphEvenHeadSynthesis i c0 c) =
      c0 • V_n_m i 0 +
        ∑ n : Fin R, c n •
          (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ •
            (V_n_m i (n.val + 1 : ℕ) +
              V_n_m i (-((n.val + 1 : ℕ) : ℤ)))) := by
  unfold sourceWeilGraphEvenHeadSynthesis
  rw [map_add, map_smul, sourceWeilGraphAmbient_evenZeroMode,
    sourceWeilGraphAmbient_evenNonzeroLowBandSynthesis]

/-- Every finite nonzero-even low-band synthesis is ambient-orthogonal to the
closed nonzero-even tail beyond cutoff `R`. -/
theorem sourceWeilGraphEvenNonzeroLowBandSynthesis_orthogonal_tail
    (i : PairIndex) (R : ℕ) (c : Fin R → ℂ)
    (x : SourceWeilGraphEvenNonzeroTailCarrier i R) :
    inner ℂ
        (sourceWeilGraphAmbient i
          (sourceWeilGraphEvenNonzeroLowBandSynthesis i c))
        (sourceWeilGraphAmbient i (x : SourceWeilGraphCarrier i)) = 0 := by
  rw [sourceWeilGraphAmbient_evenNonzeroLowBandSynthesis]
  classical
  rw [← inner_conj_symm, inner_sum]
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro n hn
  have hle : n.val + 1 ≤ R := by
    omega
  have hpos : Int.natAbs ((n.val + 1 : ℕ) : ℤ) ≤ R := by
    simpa using hle
  have hneg : Int.natAbs (-((n.val + 1 : ℕ) : ℤ)) ≤ R := by
    rw [Int.natAbs_neg, Int.natAbs_natCast]
    exact hle
  have hvpos :
      inner ℂ (sourceWeilGraphAmbient i (x : SourceWeilGraphCarrier i))
        (V_n_m i ((n.val + 1 : ℕ) : ℤ)) = 0 := by
    rw [← inner_conj_symm,
      sourceWeilGraphEvenNonzeroTail_low_fourier_vanish i R x
        ((n.val + 1 : ℕ) : ℤ) hpos]
    simp
  have hvneg :
      inner ℂ (sourceWeilGraphAmbient i (x : SourceWeilGraphCarrier i))
        (V_n_m i (-((n.val + 1 : ℕ) : ℤ))) = 0 := by
    rw [← inner_conj_symm,
      sourceWeilGraphEvenNonzeroTail_low_fourier_vanish i R x
        (-((n.val + 1 : ℕ) : ℤ)) hneg]
    simp
  rw [inner_smul_right, inner_smul_right, inner_add_right, hvpos, hvneg]
  simp

/-- The full zero-plus-low-band source-even head is ambient-orthogonal to the
closed nonzero-even tail. -/
theorem sourceWeilGraphEvenHeadSynthesis_orthogonal_tail
    (i : PairIndex) (R : ℕ) (c0 : ℂ) (c : Fin R → ℂ)
    (x : SourceWeilGraphEvenNonzeroTailCarrier i R) :
    inner ℂ
        (sourceWeilGraphAmbient i
          (sourceWeilGraphEvenHeadSynthesis i c0 c))
        (sourceWeilGraphAmbient i (x : SourceWeilGraphCarrier i)) = 0 := by
  rw [sourceWeilGraphAmbient_evenHeadSynthesis, inner_add_left,
    inner_smul_left]
  have hzero := sourceWeilGraphEvenZeroMode_orthogonal_nonzeroTail i R x
  rw [sourceWeilGraphAmbient_evenZeroMode] at hzero
  rw [hzero]
  have hlow :=
    sourceWeilGraphEvenNonzeroLowBandSynthesis_orthogonal_tail i R c x
  rw [sourceWeilGraphAmbient_evenNonzeroLowBandSynthesis] at hlow
  rw [hlow]
  simp

#print axioms sourceWeilGraphAmbient_evenNonzeroMode_orthonormal
#print axioms sourceWeilGraphAmbient_evenNonzeroLowBandSynthesis
#print axioms sourceWeilGraphAmbient_evenHeadSynthesis
#print axioms sourceWeilGraphEvenNonzeroLowBandSynthesis_orthogonal_tail
#print axioms sourceWeilGraphEvenHeadSynthesis_orthogonal_tail

end Q3.RouteB.D0Pstar
