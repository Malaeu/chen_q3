import Q3.Proofs.RouteB.ProlateActualModeMuntzRegularity
import Q3.Proofs.RouteB.EStarWindowedMellinCrosswalk

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# Actual prolate packets supply the D0 `E_star` carrier certificate

Knowledge preflight:
`./ask.sh --deep "Goal058 E_star MemLp compact support source window finite sum
lambda sqrt m prolateCombination"` found the existing exact
`WindowFiniteSupport` crosswalk, but no theorem deriving the production
`MemLp` certificate.

On the D0 window, `lambda_m i = sqrt i.m` and `u >= 1 / sqrt i.m`.  Hence a
packet supported on `[-lambda_m i, lambda_m i]` contributes only at positive
integer indices `n <= i.m`.  The infinite `E_star` sum is therefore the
existing finite comb, which is measurable and bounded on the finite D0
measure window.

This file supplies only the `MemLp` carrier field.  It does not construct an
actual prolate pair, prove CCM Lemma 7.2, or prove projected-trial nonvanishing
or a denominator floor.
-/

/-- Positive integer indices that can contribute on the D0 source window. -/
def sourcePositiveIndexFinset (i : PairIndex) : Finset ℕ+ :=
  Finset.Icc ⟨1, Nat.one_pos⟩
    ⟨i.m, lt_of_lt_of_le Nat.zero_lt_two i.hm⟩

private theorem lambda_m_pos (i : PairIndex) : 0 < lambda_m i := by
  rw [lambda_m]
  exact Real.sqrt_pos.2
    (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two i.hm))

private theorem lambda_m_sq (i : PairIndex) :
    lambda_m i * lambda_m i = (i.m : ℝ) := by
  rw [lambda_m, Real.mul_self_sqrt]
  positivity

/-- Compact support at the production D0 scale supplies the exact finite-sum
certificate consumed by `E_star_eq_finiteEStar_of_windowFiniteSupport`. -/
theorem prolateCombination_windowFiniteSupport
    (i : PairIndex) (P : ProlatePair)
    (hlambda : P.pw.lambda = lambda_m i) :
    WindowFiniteSupport (lambda_m i) (sourcePositiveIndexFinset i)
      (prolateCombination P) := by
  intro u hu n hn
  apply prolateCombination_eq_zero_outside P
  rw [hlambda]
  intro hx
  have hnlt : i.m < (n : ℕ) := by
    have hnnot :
        ¬ n ≤
          (⟨i.m, lt_of_lt_of_le Nat.zero_lt_two i.hm⟩ : ℕ+) := by
      intro hnle
      exact hn (Finset.mem_Icc.mpr ⟨by exact n.prop, hnle⟩)
    exact Nat.lt_of_not_ge (fun hle => hnnot hle)
  have hlam : 0 < lambda_m i := lambda_m_pos i
  have hnreal : (i.m : ℝ) < ((n : ℕ) : ℝ) := by
    exact_mod_cast hnlt
  have hmul : ((n : ℕ) : ℝ) * (lambda_m i)⁻¹ ≤
      ((n : ℕ) : ℝ) * u := by
    exact mul_le_mul_of_nonneg_left hu.1 (by positivity)
  have hstrict : lambda_m i <
      ((n : ℕ) : ℝ) * (lambda_m i)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (lt_div_iff₀ hlam).2
    rw [lambda_m_sq]
    exact hnreal
  linarith [hx.2]

/-- An actual source-locked prolate packet has the exact `MemLp` certificate
needed by the production `gTrial_m` constructor.  In particular, the
`eStar_memLp` field is a theorem consequence once an actual pair at the D0
scale exists; it need not be postulated independently. -/
theorem prolateCombination_E_star_memLp_of_actualModes
    (i : PairIndex) (P : ProlatePair)
    (hlambda : P.pw.lambda = lambda_m i)
    (hP : IsActualProlateModePair P) :
    MemLp (E_star (prolateCombination P)) 2
      (dStar.restrict (I_m i)) := by
  let h := prolateCombination P
  let S := sourcePositiveIndexFinset i
  obtain ⟨K, _heven, hmeas, hsupp, hlip, _hmass⟩ :=
    prolateCombination_muntzRegularity_of_actualModes P hP
  rw [hlambda] at hsupp hlip
  have hlam : 0 < lambda_m i := lambda_m_pos i
  have hfinite : WindowFiniteSupport (lambda_m i) S h := by
    simpa only [h, S] using
      prolateCombination_windowFiniteSupport i P hlambda
  have hfiniteMeas : Measurable (finiteEStar S h) := by
    unfold finiteEStar finiteEStarCore
    fun_prop
  let C : ℝ :=
    ‖h 0‖ + (K : ℝ) * lambda_m i + ‖h (lambda_m i)‖
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hhbound : ∀ x : ℝ, 0 ≤ x → ‖h x‖ ≤ C := by
    intro x hx
    by_cases hxl : x < lambda_m i
    · have hxmem : x ∈ Ico (0 : ℝ) (lambda_m i) := ⟨hx, hxl⟩
      have h0mem : (0 : ℝ) ∈ Ico (0 : ℝ) (lambda_m i) :=
        ⟨le_rfl, hlam⟩
      have hd := hlip.dist_le_mul x hxmem 0 h0mem
      have hnorm : ‖h x‖ ≤ ‖h 0‖ + dist (h x) (h 0) :=
        norm_le_norm_add_norm_sub' (h x) (h 0)
      calc
        ‖h x‖ ≤ ‖h 0‖ + dist (h x) (h 0) := hnorm
        _ ≤ ‖h 0‖ + (K : ℝ) * dist x 0 := by gcongr
        _ ≤ ‖h 0‖ + (K : ℝ) * lambda_m i := by
          simp only [Real.dist_eq, sub_zero, abs_of_nonneg hx]
          gcongr
        _ ≤ C := by
          dsimp [C]
          exact le_add_of_nonneg_right (norm_nonneg _)
    · have hlex : lambda_m i ≤ x := le_of_not_gt hxl
      by_cases heq : x = lambda_m i
      · subst x
        dsimp [C]
        nlinarith [norm_nonneg (h 0),
          mul_nonneg K.coe_nonneg hlam.le]
      · have hout : x ∉ Icc (-(lambda_m i)) (lambda_m i) := by
          intro hxmem
          exact heq (le_antisymm hxmem.2 hlex)
        have hz : h x = 0 := by
          apply hsupp x
          simpa [hlambda] using hout
        rw [hz, norm_zero]
        exact hC
  let B : ℝ :=
    Real.sqrt (lambda_m i) * (S.card : ℝ) * C
  have hfiniteBound : ∀ u ∈ I_m i, ‖finiteEStar S h u‖ ≤ B := by
    intro u hu
    have hu0 : 0 ≤ u := (inv_pos.mpr hlam).le.trans hu.1
    have hsqrt : Real.sqrt u ≤ Real.sqrt (lambda_m i) :=
      Real.sqrt_le_sqrt hu.2
    have hsum :
        ‖finiteEStarCore S h u‖ ≤ (S.card : ℝ) * C := by
      calc
        ‖finiteEStarCore S h u‖ ≤
            ∑ n ∈ S, ‖h (((n : ℕ) : ℝ) * u)‖ := by
          unfold finiteEStarCore
          exact norm_sum_le _ _
        _ ≤ ∑ n ∈ S, C := by
          gcongr with n hn
          apply hhbound
          positivity
        _ = (S.card : ℝ) * C := by simp
    rw [finiteEStar, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg u)]
    dsimp [B]
    calc
      Real.sqrt u * ‖finiteEStarCore S h u‖ ≤
          Real.sqrt (lambda_m i) * ((S.card : ℝ) * C) :=
        mul_le_mul hsqrt hsum (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt (lambda_m i) * (S.card : ℝ) * C := by ring
  letI : IsFiniteMeasure (dStar.restrict (I_m i)) :=
    ⟨by
      rw [Measure.restrict_apply_univ, dStar, I_m,
        withDensity_apply _ measurableSet_Icc]
      have hinv : IntegrableOn (fun u : ℝ => u⁻¹) (I_m i) volume := by
        apply ContinuousOn.integrableOn_Icc
        apply continuousOn_id.inv₀
        intro u hu
        exact ne_of_gt ((inv_pos.mpr hlam).trans_le hu.1)
      simpa [I_m] using hinv.setLIntegral_lt_top⟩
  have hfiniteLp : MemLp (finiteEStar S h) 2
      (dStar.restrict (I_m i)) := by
    apply MemLp.of_bound hfiniteMeas.aestronglyMeasurable B
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact hfiniteBound u hu
  have heq :
      finiteEStar S h =ᵐ[dStar.restrict (I_m i)] E_star h := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact
      (E_star_eq_finiteEStar_of_windowFiniteSupport hfinite hu).symm
  simpa only [h] using MemLp.ae_eq heq hfiniteLp

#print axioms sourcePositiveIndexFinset
#print axioms prolateCombination_windowFiniteSupport
#print axioms prolateCombination_E_star_memLp_of_actualModes

end Q3.RouteB.D0Pstar
