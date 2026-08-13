import Q3.Proofs.RouteB.D0PstarCCMFiniteSourceResidual
import Q3.Proofs.RouteB.CCMFiniteWeilParity

set_option linter.mathlibStandardSet false

open Complex Matrix
open scoped BigOperators

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# Exact source CCM odd mass as a reflection defect

This file keeps the literal complex coefficient row of the normalized projected
source trial.  It neither replaces that row by its real part nor symmetrizes the
trial.  The exact odd mass is represented as one quarter of the squared norm of
the difference between the source trial and the finite synthesis of its
reflected coefficient row.

The result is a finite-dimensional identity valid for every `PairIndex`.  It
does not prove that the odd mass vanishes or decays along a cofinal family, and
it makes no spectral-gap, ground-state, Route B promotion, or RH claim.
-/

/-- The exact reflection-odd part of the literal complex source row. -/
noncomputable def sourceCCMComplexOddPart
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) :
    CCMModeFinite i.N → ℂ :=
  fun j =>
    (sourceCCMComplexRow S i j -
      sourceCCMComplexRow S i (ccmNegFinite i.N j)) / 2

/-- Squared Euclidean mass of the exact reflection-odd source row. -/
noncomputable def sourceCCMComplexOddMass
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) : ℝ :=
  ∑ j, Complex.normSq (sourceCCMComplexOddPart S i j)

/-- Finite synthesis of the exact source row after coefficient reflection. -/
noncomputable def sourceCCMReflectedFiniteTrial
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) : H_m i :=
  ccmFiniteSynthesis i
    (fun j => sourceCCMComplexRow S i (ccmNegFinite i.N j))

/-- Difference between the literal normalized projected source trial and the
finite synthesis of its reflected coefficient row. -/
noncomputable def sourceCCMFiniteReflectionDefect
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) : H_m i :=
  (kTrial_m_N
      i
      (prolateCombination (S.source.pair i))
      (S.source.eStar_memLp i)
      (S.source.trialNonzero i) : H_m i) -
    sourceCCMReflectedFiniteTrial S i

private theorem ccmModeFinite_injective_local (N : ℕ) :
    Function.Injective (ccmModeFinite N) := by
  intro j k h
  apply Fin.ext
  simpa [ccmModeFinite] using h

private theorem norm_ccmFiniteSynthesis_sq
    (i : PairIndex)
    (c : CCMModeFinite i.N → ℂ) :
    ‖ccmFiniteSynthesis i c‖ ^ 2 =
      ∑ j, Complex.normSq (c j) := by
  classical
  have horth :
      Orthonormal ℂ
        (fun j : CCMModeFinite i.N => V_n_m i (ccmModeFinite i.N j)) :=
    (V_n_m_orthonormal i).comp (ccmModeFinite i.N)
      (ccmModeFinite_injective_local i.N)
  have hinner :
      inner ℂ (ccmFiniteSynthesis i c) (ccmFiniteSynthesis i c) =
        ((∑ j, Complex.normSq (c j) : ℝ) : ℂ) := by
    unfold ccmFiniteSynthesis
    simpa [Complex.normSq_eq_conj_mul_self] using
      horth.inner_sum c c Finset.univ
  calc
    ‖ccmFiniteSynthesis i c‖ ^ 2 =
        (inner ℂ (ccmFiniteSynthesis i c) (ccmFiniteSynthesis i c)).re :=
      by simpa using
        (norm_sq_eq_re_inner (𝕜 := ℂ) (ccmFiniteSynthesis i c))
    _ = ∑ j, Complex.normSq (c j) := by rw [hinner]; simp

theorem sourceCCMFiniteReflectionDefect_eq_synthesis_sub_reflection
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) :
    sourceCCMFiniteReflectionDefect S i =
      ccmFiniteSynthesis i
        (fun j =>
          sourceCCMComplexRow S i j -
            sourceCCMComplexRow S i (ccmNegFinite i.N j)) := by
  unfold sourceCCMFiniteReflectionDefect sourceCCMReflectedFiniteTrial
  rw [← ccmFiniteSynthesis_sourceCCMComplexRow S i]
  change
    ccmFiniteSynthesis i (sourceCCMComplexRow S i) -
        ccmFiniteSynthesis i
          (fun j => sourceCCMComplexRow S i (ccmNegFinite i.N j)) =
      ccmFiniteSynthesis i
        (sourceCCMComplexRow S i -
          fun j => sourceCCMComplexRow S i (ccmNegFinite i.N j))
  exact ((ccmFiniteSynthesis i).map_sub _ _).symm

/-- The exact odd-mass identity selected by the Goal 058 parity-sector route.
The factor `1/4` is forced by `q₋ = (q - Jq) / 2`. -/
theorem sourceCCMComplexOddMass_eq_quarter_norm_reflectionDefect_sq
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) :
    sourceCCMComplexOddMass S i =
      (1 / 4 : ℝ) * ‖sourceCCMFiniteReflectionDefect S i‖ ^ 2 := by
  rw [sourceCCMFiniteReflectionDefect_eq_synthesis_sub_reflection,
    norm_ccmFiniteSynthesis_sq]
  unfold sourceCCMComplexOddMass sourceCCMComplexOddPart
  simp_rw [Complex.normSq_div]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  norm_num [Complex.normSq]
  ring

theorem sourceCCMComplexOddMass_nonneg
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) :
    0 ≤ sourceCCMComplexOddMass S i := by
  unfold sourceCCMComplexOddMass
  exact Finset.sum_nonneg fun j hj => Complex.normSq_nonneg _

/-- A source-faithful analytic supplier can bound the odd mass by giving one
ambient vector whose retained Fourier coefficients are the reflected source
coefficients.  Bessel's inequality then pays only the physical approximation
error.  No such ambient supplier is manufactured here. -/
theorem sourceCCMComplexOddMass_le_quarter_norm_sub_sq_of_reflected_coefficients
    (S : ProlateCanonicalSourceData)
    (i : PairIndex)
    (f : H_m i)
    (hreflect : ∀ j : CCMModeFinite i.N,
      inner ℂ (V_n_m i (ccmModeFinite i.N j)) f =
        sourceCCMComplexRow S i (ccmNegFinite i.N j)) :
    sourceCCMComplexOddMass S i ≤
      (1 / 4 : ℝ) *
        ‖(kTrial_m_N
            i
            (prolateCombination (S.source.pair i))
            (S.source.eStar_memLp i)
            (S.source.trialNonzero i) : H_m i) - f‖ ^ 2 := by
  classical
  let k : H_m i :=
    (kTrial_m_N
      i
      (prolateCombination (S.source.pair i))
      (S.source.eStar_memLp i)
      (S.source.trialNonzero i) : H_m i)
  have horth :
      Orthonormal ℂ
        (fun j : CCMModeFinite i.N => V_n_m i (ccmModeFinite i.N j)) :=
    (V_n_m_orthonormal i).comp (ccmModeFinite i.N)
      (ccmModeFinite_injective_local i.N)
  have hterms :
      (∑ j,
          Complex.normSq
            (sourceCCMComplexRow S i j -
              sourceCCMComplexRow S i (ccmNegFinite i.N j))) =
        ∑ j,
          ‖inner ℂ (V_n_m i (ccmModeFinite i.N j)) (k - f)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    have hrow :
        sourceCCMComplexRow S i j =
          inner ℂ (V_n_m i (ccmModeFinite i.N j)) k := by
      simp [k, sourceCCMComplexRow_apply, c_n]
    rw [hrow, ← hreflect j, ← inner_sub_right, Complex.normSq_eq_norm_sq]
  have hbessel :
      (∑ j,
          ‖inner ℂ (V_n_m i (ccmModeFinite i.N j)) (k - f)‖ ^ 2) ≤
        ‖k - f‖ ^ 2 := by
    simpa using (horth.sum_inner_products_le (x := k - f)
      (s := Finset.univ))
  have hmass :
      sourceCCMComplexOddMass S i =
        (1 / 4 : ℝ) *
          ∑ j,
            Complex.normSq
              (sourceCCMComplexRow S i j -
                sourceCCMComplexRow S i (ccmNegFinite i.N j)) := by
    unfold sourceCCMComplexOddMass sourceCCMComplexOddPart
    simp_rw [Complex.normSq_div]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    norm_num [Complex.normSq]
    ring
  rw [hmass, hterms]
  exact mul_le_mul_of_nonneg_left hbessel (by norm_num)

/-- A physical approximant whose retained source coefficients are reflection
even controls the entire exact odd mass.  This is the non-circular receiver
for the inversion-even continuum packet: the source row is not symmetrized,
and the right side is an actual ambient approximation error. -/
theorem sourceCCMComplexOddMass_le_norm_sub_sq_of_even_coefficients
    (S : ProlateCanonicalSourceData)
    (i : PairIndex)
    (f : H_m i)
    (heven : ∀ j : CCMModeFinite i.N,
      inner ℂ (V_n_m i (ccmModeFinite i.N (ccmNegFinite i.N j))) f =
        inner ℂ (V_n_m i (ccmModeFinite i.N j)) f) :
    sourceCCMComplexOddMass S i ≤
      ‖(kTrial_m_N
          i
          (prolateCombination (S.source.pair i))
          (S.source.eStar_memLp i)
          (S.source.trialNonzero i) : H_m i) - f‖ ^ 2 := by
  classical
  let k : H_m i :=
    (kTrial_m_N
      i
      (prolateCombination (S.source.pair i))
      (S.source.eStar_memLp i)
      (S.source.trialNonzero i) : H_m i)
  let x : CCMModeFinite i.N → ℂ := fun j =>
    sourceCCMComplexRow S i j -
      inner ℂ (V_n_m i (ccmModeFinite i.N j)) f
  have hdiff (j : CCMModeFinite i.N) :
      sourceCCMComplexRow S i j -
          sourceCCMComplexRow S i (ccmNegFinite i.N j) =
        x j - x (ccmNegFinite i.N j) := by
    dsimp only [x]
    rw [heven j]
    ring
  have hpoint (j : CCMModeFinite i.N) :
      (1 / 4 : ℝ) * Complex.normSq
          (sourceCCMComplexRow S i j -
            sourceCCMComplexRow S i (ccmNegFinite i.N j)) ≤
        (1 / 2 : ℝ) *
          (Complex.normSq (x j) +
            Complex.normSq (x (ccmNegFinite i.N j))) := by
    rw [hdiff, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    have htri := norm_sub_le (x j) (x (ccmNegFinite i.N j))
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hdiffsq :=
      sq_nonneg (‖x j‖ - ‖x (ccmNegFinite i.N j)‖)
    nlinarith
  let negEquiv : CCMModeFinite i.N ≃ CCMModeFinite i.N :=
    { toFun := ccmNegFinite i.N
      invFun := ccmNegFinite i.N
      left_inv := ccmNegFinite_involutive i.N
      right_inv := ccmNegFinite_involutive i.N }
  have hnegSum :
      (∑ j, Complex.normSq (x (ccmNegFinite i.N j))) =
        ∑ j, Complex.normSq (x j) := by
    simpa [negEquiv] using
      (negEquiv.sum_comp (fun j => Complex.normSq (x j)))
  have hsum :
      (1 / 4 : ℝ) *
          ∑ j, Complex.normSq
            (sourceCCMComplexRow S i j -
              sourceCCMComplexRow S i (ccmNegFinite i.N j)) ≤
        ∑ j, Complex.normSq (x j) := by
    rw [Finset.mul_sum]
    calc
      (∑ j, (1 / 4 : ℝ) * Complex.normSq
          (sourceCCMComplexRow S i j -
            sourceCCMComplexRow S i (ccmNegFinite i.N j))) ≤
          ∑ j, (1 / 2 : ℝ) *
            (Complex.normSq (x j) +
              Complex.normSq (x (ccmNegFinite i.N j))) := by
        exact Finset.sum_le_sum fun j hj => hpoint j
      _ = ∑ j, Complex.normSq (x j) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, hnegSum]
        ring
  have hterms :
      (∑ j, Complex.normSq (x j)) =
        ∑ j,
          ‖inner ℂ (V_n_m i (ccmModeFinite i.N j)) (k - f)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    have hrow :
        sourceCCMComplexRow S i j =
          inner ℂ (V_n_m i (ccmModeFinite i.N j)) k := by
      simp [k, sourceCCMComplexRow_apply, c_n]
    dsimp only [x]
    rw [hrow, ← inner_sub_right, Complex.normSq_eq_norm_sq]
  have horth :
      Orthonormal ℂ
        (fun j : CCMModeFinite i.N => V_n_m i (ccmModeFinite i.N j)) :=
    (V_n_m_orthonormal i).comp (ccmModeFinite i.N)
      (ccmModeFinite_injective_local i.N)
  have hbessel :
      (∑ j,
          ‖inner ℂ (V_n_m i (ccmModeFinite i.N j)) (k - f)‖ ^ 2) ≤
        ‖k - f‖ ^ 2 := by
    simpa using (horth.sum_inner_products_le (x := k - f)
      (s := Finset.univ))
  have hmass :
      sourceCCMComplexOddMass S i =
        (1 / 4 : ℝ) *
          ∑ j, Complex.normSq
            (sourceCCMComplexRow S i j -
              sourceCCMComplexRow S i (ccmNegFinite i.N j)) := by
    unfold sourceCCMComplexOddMass sourceCCMComplexOddPart
    simp_rw [Complex.normSq_div]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    norm_num [Complex.normSq]
    ring
  rw [hmass]
  exact hsum.trans (hterms ▸ hbessel)

#print axioms sourceCCMFiniteReflectionDefect_eq_synthesis_sub_reflection
#print axioms sourceCCMComplexOddMass_eq_quarter_norm_reflectionDefect_sq
#print axioms sourceCCMComplexOddMass_nonneg
#print axioms sourceCCMComplexOddMass_le_quarter_norm_sub_sq_of_reflected_coefficients
#print axioms sourceCCMComplexOddMass_le_norm_sub_sq_of_even_coefficients

end Q3.RouteB.D0Pstar
