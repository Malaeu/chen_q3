import Q3.Proofs.RouteB.D0KTrialStage2
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Finite-window Mellin crosswalk for the D0 starred packet

This file keeps the time-side input `h` parametric.  The first theorem is a
finite-window identity; it never interchanges an infinite sum and an integral.
The zero-mass hypothesis is registered separately for the Müntz continuation
front.
-/

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace Q3.RouteB.D0Pstar

/-- The multiplicative source window `[lambda⁻¹, lambda]`. -/
def sourceWindow (lambda : ℝ) : Set ℝ :=
  Set.Icc lambda⁻¹ lambda

/-- The image of the source window under multiplication by a positive integer. -/
def scaledSourceWindow (lambda : ℝ) (n : ℕ+) : Set ℝ :=
  Set.Icc (((n : ℕ) : ℝ) * lambda⁻¹) (((n : ℕ) : ℝ) * lambda)

/-- The finite unstarred comb appearing on a source window. -/
def finiteEStarCore (S : Finset ℕ+) (h : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∑ n ∈ S, h (((n : ℕ) : ℝ) * u)

/-- The finite starred comb, using the exact D0 square-root convention. -/
def finiteEStar (S : Finset ℕ+) (h : ℝ → ℂ) (u : ℝ) : ℂ :=
  (Real.sqrt u : ℂ) * finiteEStarCore S h u

/-- A support certificate saying that the infinite starred comb is finite on
the selected source window.  This is the precise support hypothesis used to
connect the parametric finite identity to `E_star`. -/
def WindowFiniteSupport
    (lambda : ℝ) (S : Finset ℕ+) (h : ℝ → ℂ) : Prop :=
  ∀ u ∈ sourceWindow lambda, ∀ n : ℕ+, n ∉ S →
    h (((n : ℕ) : ℝ) * u) = 0

/-- The finite Dirichlet window
`sum_{n in S} n^(-p) 1_[n/lambda,n*lambda](v)`. -/
def dirichletWindow
    (lambda : ℝ) (S : Finset ℕ+) (p : ℂ) (v : ℝ) : ℂ :=
  ∑ n ∈ S,
    (n : ℂ) ^ (-p) *
      (scaledSourceWindow lambda n).indicator (fun _ : ℝ => (1 : ℂ)) v

/-- Mellin transform after restriction to the exact source window. -/
def windowedMellin (lambda : ℝ) (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  mellin ((sourceWindow lambda).indicator f) s

/-- The right-hand side of the finite-window Mellin identity. -/
def weightedDirichletWindowIntegral
    (lambda : ℝ) (S : Finset ℕ+) (h : ℝ → ℂ) (p : ℂ) : ℂ :=
  ∫ v : ℝ in Set.Ioi 0,
    (v : ℂ) ^ (p - 1) * h v * dirichletWindow lambda S p v

/-- The unstarred positive-integer comb. -/
def eStarCore (h : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∑' n : ℕ+, h (((n : ℕ) : ℝ) * u)

/-- Exact zero positive-half mass; this is kept as an explicit hypothesis in
the zero-mass branch. -/
def ZeroPositiveMass (h : ℝ → ℂ) : Prop :=
  (∫ v : ℝ in Set.Ioi 0, h v) = 0

/-- Absolute-convergence data sufficient for the unwindowed sum/integral
interchange at Mellin exponent `p`. -/
def EStarMellinAbsolute (h : ℝ → ℂ) (p : ℂ) : Prop :=
  (∀ n : ℕ+,
    AEStronglyMeasurable
      (fun u : ℝ =>
        (u : ℂ) ^ (p - 1) • h (((n : ℕ) : ℝ) * u))
      (volume.restrict (Set.Ioi 0))) ∧
  (∑' n : ℕ+,
      ∫⁻ u : ℝ,
        ‖(u : ℂ) ^ (p - 1) •
          h (((n : ℕ) : ℝ) * u)‖ₑ
        ∂(volume.restrict (Set.Ioi 0))) ≠ ⊤

/-- Lower omitted Mellin tail. -/
def lowerMellinTail (lambda : ℝ) (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  mellin ((Set.Iio lambda⁻¹).indicator f) s

/-- Upper omitted Mellin tail. -/
def upperMellinTail (lambda : ℝ) (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  mellin ((Set.Ioi lambda).indicator f) s

/-- The mandatory nonzero-mass pole plant: the unit step on `(0,1]`.

This indicator is deliberately discontinuous.  It detects the pole
counterterm and is not a plant for the T2 regularity class.  A triangular
Lipschitz PL2 remains a separate obligation of the repaired v2 continuation
contract. -/
def nonzeroMassPlant (v : ℝ) : ℝ :=
  (Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) v

/-- Closed real form of the pole-window factor
`J_lambda(t)=integral_[lambda⁻¹,lambda] u^(t-3/2) du`. -/
def poleWindowJReal (lambda t : ℝ) : ℝ :=
  (lambda ^ (1 / 2 - t) - lambda ^ (t - 1 / 2)) / (1 / 2 - t)

/-- Exact normalized growth factor extracted from
`J_lambda(-sigma)/J_lambda(0)`. -/
def poleRatioModel (lambda sigma : ℝ) : ℝ :=
  lambda ^ sigma / (1 + 2 * sigma) *
    ((1 - lambda ^ (-1 - 2 * sigma)) / (1 - lambda⁻¹))

theorem E_star_eq_finiteEStar_of_windowFiniteSupport
    {lambda : ℝ} {S : Finset ℕ+} {h : ℝ → ℂ}
    (hfinite : WindowFiniteSupport lambda S h)
    {u : ℝ} (hu : u ∈ sourceWindow lambda) :
    E_star h u = finiteEStar S h u := by
  unfold E_star finiteEStar finiteEStarCore
  congr 1
  exact (hasSum_sum_of_ne_finset_zero (hfinite u hu)).tsum_eq

theorem indicator_scaledSourceWindow_comp
    {lambda : ℝ} (n : ℕ+)
    (h : ℝ → ℂ) (u : ℝ) :
    (scaledSourceWindow lambda n).indicator h (((n : ℕ) : ℝ) * u) =
      (sourceWindow lambda).indicator
        (fun x => h (((n : ℕ) : ℝ) * x)) u := by
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by positivity
  have hmem :
      (((n : ℕ) : ℝ) * u ∈ scaledSourceWindow lambda n) ↔
        u ∈ sourceWindow lambda := by
    simp only [scaledSourceWindow, sourceWindow, Set.mem_Icc]
    constructor
    · intro hnu
      constructor <;> nlinarith [hnu.1, hnu.2]
    · intro hu
      constructor <;> nlinarith [hu.1, hu.2]
  by_cases hu : u ∈ sourceWindow lambda
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (hmem.mpr hu)]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem]
    exact mt hmem.mp hu

theorem mem_scaledSourceWindow_iff
    {lambda : ℝ} (hlambda : 0 < lambda) (n : ℕ+) (v : ℝ) :
    v ∈ scaledSourceWindow lambda n ↔
      v / lambda ≤ ((n : ℕ) : ℝ) ∧
        ((n : ℕ) : ℝ) ≤ v * lambda := by
  simp only [scaledSourceWindow, Set.mem_Icc]
  constructor
  · intro hv
    constructor
    · exact (div_le_iff₀ hlambda).mpr hv.2
    · have := (div_le_iff₀ hlambda).mp
        (show ((n : ℕ) : ℝ) / lambda ≤ v by
          simpa [div_eq_mul_inv] using hv.1)
      simpa [mul_comm] using this
  · intro hv
    constructor
    · have := (div_le_iff₀ hlambda).mpr (by simpa [mul_comm] using hv.2)
      simpa [div_eq_mul_inv] using this
    · exact (div_le_iff₀ hlambda).mp hv.1

theorem dirichletWindow_eq_constraint_sum
    {lambda : ℝ} (hlambda : 0 < lambda)
    (S : Finset ℕ+) (p : ℂ) (v : ℝ) :
    dirichletWindow lambda S p v =
      ∑ n ∈ S,
        if v / lambda ≤ ((n : ℕ) : ℝ) ∧
            ((n : ℕ) : ℝ) ≤ v * lambda then
          (n : ℂ) ^ (-p)
        else 0 := by
  unfold dirichletWindow
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hv :
      v / lambda ≤ ((n : ℕ) : ℝ) ∧
        ((n : ℕ) : ℝ) ≤ v * lambda
  · have hmem : v ∈ scaledSourceWindow lambda n :=
      (mem_scaledSourceWindow_iff hlambda n v).mpr hv
    simp [hv, hmem]
  · have hnotmem : v ∉ scaledSourceWindow lambda n := by
      exact fun hmem => hv ((mem_scaledSourceWindow_iff hlambda n v).mp hmem)
    simp [hv, hnotmem]

theorem mellin_windowed_scaled
    {lambda : ℝ} (n : ℕ+)
    (h : ℝ → ℂ) (p : ℂ) :
    mellin
        ((sourceWindow lambda).indicator
          (fun u => h (((n : ℕ) : ℝ) * u))) p =
      (n : ℂ) ^ (-p) *
        mellin ((scaledSourceWindow lambda n).indicator h) p := by
  calc
    mellin
        ((sourceWindow lambda).indicator
          (fun u => h (((n : ℕ) : ℝ) * u))) p =
        mellin
          (fun u =>
            (scaledSourceWindow lambda n).indicator h
              (((n : ℕ) : ℝ) * u)) p := by
      congr 1
      funext u
      exact (indicator_scaledSourceWindow_comp n h u).symm
    _ = (n : ℂ) ^ (-p) *
        mellin ((scaledSourceWindow lambda n).indicator h) p := by
      simpa only [smul_eq_mul] using
        mellin_comp_mul_left
          ((scaledSourceWindow lambda n).indicator h) p
          (show (0 : ℝ) < ((n : ℕ) : ℝ) by positivity)

theorem mellinConvergent_windowed_scaled_iff
    {lambda : ℝ} (n : ℕ+)
    (h : ℝ → ℂ) (p : ℂ) :
    MellinConvergent
        ((sourceWindow lambda).indicator
          (fun u => h (((n : ℕ) : ℝ) * u))) p ↔
      MellinConvergent ((scaledSourceWindow lambda n).indicator h) p := by
  have hfun :
      (sourceWindow lambda).indicator
          (fun u => h (((n : ℕ) : ℝ) * u)) =
        fun u =>
          (scaledSourceWindow lambda n).indicator h
            (((n : ℕ) : ℝ) * u) := by
    funext u
    exact (indicator_scaledSourceWindow_comp n h u).symm
  rw [hfun]
  exact MellinConvergent.comp_mul_left
    (show (0 : ℝ) < ((n : ℕ) : ℝ) by positivity)

theorem windowedMellin_finiteEStarCore_eq_sum
    {lambda : ℝ} {S : Finset ℕ+} {h : ℝ → ℂ} {p : ℂ}
    (hconv :
      ∀ n ∈ S,
        MellinConvergent
          ((sourceWindow lambda).indicator
            (fun u => h (((n : ℕ) : ℝ) * u))) p) :
    windowedMellin lambda (finiteEStarCore S h) p =
      ∑ n ∈ S,
        mellin
          ((sourceWindow lambda).indicator
            (fun u => h (((n : ℕ) : ℝ) * u))) p := by
  unfold windowedMellin mellin finiteEStarCore
  rw [← MeasureTheory.integral_finset_sum S]
  · apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    by_cases hu : u ∈ sourceWindow lambda
    · simp only [Set.indicator_of_mem hu, Finset.smul_sum]
    · simp only [Set.indicator_of_notMem hu, smul_zero]
      exact (Finset.sum_const_zero).symm
  · intro n hn
    exact hconv n hn

theorem windowedMellin_finiteEStarCore_eq_dirichlet_sum
    {lambda : ℝ}
    {S : Finset ℕ+} {h : ℝ → ℂ} {p : ℂ}
    (hconv :
      ∀ n ∈ S,
        MellinConvergent
          ((sourceWindow lambda).indicator
            (fun u => h (((n : ℕ) : ℝ) * u))) p) :
    windowedMellin lambda (finiteEStarCore S h) p =
      ∑ n ∈ S,
        (n : ℂ) ^ (-p) *
          mellin ((scaledSourceWindow lambda n).indicator h) p := by
  rw [windowedMellin_finiteEStarCore_eq_sum hconv]
  apply Finset.sum_congr rfl
  intro n hn
  exact mellin_windowed_scaled n h p

theorem finiteEStar_eq_cpow_mul_core
    {S : Finset ℕ+} {h : ℝ → ℂ} {u : ℝ} (hu : 0 < u) :
    finiteEStar S h u =
      (u : ℂ) ^ ((1 : ℂ) / 2) * finiteEStarCore S h u := by
  unfold finiteEStar
  congr 1
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hu.le]
  norm_num

theorem windowedMellin_finiteEStar_eq_shift
    {lambda : ℝ} (hlambda : 0 < lambda)
    (S : Finset ℕ+) (h : ℝ → ℂ) (s : ℂ) :
    windowedMellin lambda (finiteEStar S h) s =
      windowedMellin lambda (finiteEStarCore S h) (s + 1 / 2) := by
  unfold windowedMellin
  have hfun :
      (sourceWindow lambda).indicator (finiteEStar S h) =
        fun u : ℝ =>
          (u : ℂ) ^ ((1 : ℂ) / 2) •
            (sourceWindow lambda).indicator (finiteEStarCore S h) u := by
    funext u
    by_cases hu : u ∈ sourceWindow lambda
    · have hu_pos : 0 < u := by
        have hlambda_inv : 0 < lambda⁻¹ := inv_pos.mpr hlambda
        exact hlambda_inv.trans_le hu.1
      rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
      simp only [smul_eq_mul]
      exact finiteEStar_eq_cpow_mul_core hu_pos
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
      simp
  rw [hfun, mellin_cpow_smul]

theorem mul_dirichletWindow_eq_indicator_sum
    (lambda : ℝ) (S : Finset ℕ+) (h : ℝ → ℂ) (p : ℂ) (v : ℝ) :
    h v * dirichletWindow lambda S p v =
      ∑ n ∈ S,
        (n : ℂ) ^ (-p) *
          (scaledSourceWindow lambda n).indicator h v := by
  unfold dirichletWindow
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hv : v ∈ scaledSourceWindow lambda n
  · simp only [Set.indicator_of_mem hv]
    ring
  · simp only [Set.indicator_of_notMem hv, mul_zero]

theorem weightedDirichletWindowIntegral_eq_sum
    {lambda : ℝ} {S : Finset ℕ+} {h : ℝ → ℂ} {p : ℂ}
    (hconv :
      ∀ n ∈ S,
        MellinConvergent ((scaledSourceWindow lambda n).indicator h) p) :
    weightedDirichletWindowIntegral lambda S h p =
      ∑ n ∈ S,
        (n : ℂ) ^ (-p) *
          mellin ((scaledSourceWindow lambda n).indicator h) p := by
  unfold weightedDirichletWindowIntegral mellin
  simp_rw [smul_eq_mul]
  calc
    (∫ v : ℝ in Set.Ioi 0,
        (v : ℂ) ^ (p - 1) * h v * dirichletWindow lambda S p v) =
        ∫ v : ℝ in Set.Ioi 0,
          ∑ n ∈ S,
            (n : ℂ) ^ (-p) *
              ((v : ℂ) ^ (p - 1) *
                (scaledSourceWindow lambda n).indicator h v) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with v
      rw [mul_assoc, mul_dirichletWindow_eq_indicator_sum]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = ∑ n ∈ S,
          ∫ v : ℝ in Set.Ioi 0,
            (n : ℂ) ^ (-p) *
              ((v : ℂ) ^ (p - 1) *
                (scaledSourceWindow lambda n).indicator h v) := by
      rw [MeasureTheory.integral_finset_sum S]
      intro n hn
      exact (hconv n hn).const_mul _
    _ = ∑ n ∈ S,
          (n : ℂ) ^ (-p) *
            ∫ v : ℝ in Set.Ioi 0,
              (v : ℂ) ^ (p - 1) *
                (scaledSourceWindow lambda n).indicator h v := by
      apply Finset.sum_congr rfl
      intro n hn
      exact MeasureTheory.integral_const_mul _ _

/-- T1: the exact finite-window Mellin identity.  The comb is finite before
integration, and `h` remains a parameter. -/
theorem windowedMellin_finiteEStar_eq_weightedDirichletWindowIntegral
    {lambda : ℝ} (hlambda : 0 < lambda)
    {S : Finset ℕ+} {h : ℝ → ℂ} {s : ℂ}
    (hconv :
      ∀ n ∈ S,
        MellinConvergent
          ((scaledSourceWindow lambda n).indicator h) (s + 1 / 2)) :
    windowedMellin lambda (finiteEStar S h) s =
      weightedDirichletWindowIntegral lambda S h (s + 1 / 2) := by
  rw [windowedMellin_finiteEStar_eq_shift hlambda]
  rw [windowedMellin_finiteEStarCore_eq_dirichlet_sum]
  · exact (weightedDirichletWindowIntegral_eq_sum hconv).symm
  · intro n hn
    exact (mellinConvergent_windowed_scaled_iff
      n h (s + 1 / 2)).mpr (hconv n hn)

theorem windowedMellin_E_star_eq_finiteEStar
    {lambda : ℝ} {S : Finset ℕ+} {h : ℝ → ℂ}
    (hfinite : WindowFiniteSupport lambda S h) (s : ℂ) :
    windowedMellin lambda (E_star h) s =
      windowedMellin lambda (finiteEStar S h) s := by
  unfold windowedMellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  by_cases huw : u ∈ sourceWindow lambda
  · rw [Set.indicator_of_mem huw, Set.indicator_of_mem huw]
    rw [E_star_eq_finiteEStar_of_windowFiniteSupport hfinite huw]
  · rw [Set.indicator_of_notMem huw, Set.indicator_of_notMem huw]

/-- T1 in the exact `E_star` vocabulary, with the finite-support certificate
kept explicit. -/
theorem windowedMellin_E_star_eq_weightedDirichletWindowIntegral
    {lambda : ℝ} (hlambda : 0 < lambda)
    {S : Finset ℕ+} {h : ℝ → ℂ} {s : ℂ}
    (hfinite : WindowFiniteSupport lambda S h)
    (hconv :
      ∀ n ∈ S,
        MellinConvergent
          ((scaledSourceWindow lambda n).indicator h) (s + 1 / 2)) :
    windowedMellin lambda (E_star h) s =
      weightedDirichletWindowIntegral lambda S h (s + 1 / 2) := by
  rw [windowedMellin_E_star_eq_finiteEStar hfinite]
  exact windowedMellin_finiteEStar_eq_weightedDirichletWindowIntegral
    hlambda hconv

theorem E_star_eq_cpow_smul_eStarCore
    {h : ℝ → ℂ} {u : ℝ} (hu : 0 < u) :
    E_star h u =
      (u : ℂ) ^ ((1 : ℂ) / 2) • eStarCore h u := by
  unfold E_star eStarCore
  simp only [smul_eq_mul]
  congr 1
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hu.le]
  norm_num

theorem mellin_E_star_eq_shifted_core (h : ℝ → ℂ) (s : ℂ) :
    mellin (E_star h) s = mellin (eStarCore h) (s + 1 / 2) := by
  calc
    mellin (E_star h) s =
        mellin
          (fun u : ℝ =>
            (u : ℂ) ^ ((1 : ℂ) / 2) • eStarCore h u) s := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      dsimp only
      rw [E_star_eq_cpow_smul_eStarCore hu]
    _ = mellin (eStarCore h) (s + 1 / 2) := by
      rw [mellin_cpow_smul]

theorem mellin_eStarCore_eq_tsum
    {h : ℝ → ℂ} {p : ℂ} (habs : EStarMellinAbsolute h p) :
    mellin (eStarCore h) p =
      ∑' n : ℕ+,
        mellin (fun u => h (((n : ℕ) : ℝ) * u)) p := by
  unfold mellin eStarCore
  rw [show
      (fun u : ℝ =>
          (u : ℂ) ^ (p - 1) •
            ∑' n : ℕ+, h (((n : ℕ) : ℝ) * u)) =
        (fun u : ℝ =>
          ∑' n : ℕ+,
            (u : ℂ) ^ (p - 1) •
              h (((n : ℕ) : ℝ) * u)) by
    funext u
    exact (tsum_const_smul'' ((u : ℂ) ^ (p - 1))).symm]
  exact MeasureTheory.integral_tsum habs.1 habs.2

theorem pnatDirichletSeries_eq_riemannZeta
    {p : ℂ} (hp : 1 < p.re) :
    (∑' n : ℕ+, (n : ℂ) ^ (-p)) = riemannZeta p := by
  calc
    (∑' n : ℕ+, (n : ℂ) ^ (-p)) =
        ∑' k : ℕ,
          ((Nat.succPNat k : ℕ) : ℂ) ^ (-p) := by
      exact (Equiv.pnatEquivNat.symm.tsum_eq
        (fun n : ℕ+ => (n : ℂ) ^ (-p))).symm
    _ = ∑' k : ℕ, 1 / ((k + 1 : ℕ) : ℂ) ^ p := by
      apply tsum_congr
      intro k
      rw [Nat.succPNat_coe]
      simp [Complex.cpow_neg]
    _ = riemannZeta p := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (zeta_eq_tsum_one_div_nat_add_one_cpow hp).symm

theorem mellin_E_star_eq_riemannZeta_mul
    {h : ℝ → ℂ} {s : ℂ}
    (hp : 1 < (s + 1 / 2).re)
    (habs : EStarMellinAbsolute h (s + 1 / 2)) :
    mellin (E_star h) s =
      riemannZeta (s + 1 / 2) * mellin h (s + 1 / 2) := by
  rw [mellin_E_star_eq_shifted_core]
  rw [mellin_eStarCore_eq_tsum habs]
  have hscale :
      ∀ n : ℕ+,
        mellin (fun u => h (((n : ℕ) : ℝ) * u)) (s + 1 / 2) =
          (n : ℂ) ^ (-(s + 1 / 2)) • mellin h (s + 1 / 2) := by
    intro n
    exact mellin_comp_mul_left h (s + 1 / 2)
      (show (0 : ℝ) < ((n : ℕ) : ℝ) by positivity)
  simp_rw [hscale, smul_eq_mul]
  rw [tsum_mul_right]
  rw [pnatDirichletSeries_eq_riemannZeta hp]

theorem MellinConvergent.indicator_source
    {f : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent f s)
    (A : Set ℝ) (hA : MeasurableSet A) :
    MellinConvergent (A.indicator f) s := by
  unfold MellinConvergent at hf ⊢
  simpa only [← Set.indicator_smul] using hf.indicator hA

theorem mellin_eq_lower_add_window_add_upper
    {lambda : ℝ} (hlambda : 1 ≤ lambda)
    {f : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent f s) :
    mellin f s =
      lowerMellinTail lambda f s +
        windowedMellin lambda f s +
          upperMellinTail lambda f s := by
  have hlower :
      MellinConvergent ((Set.Iio lambda⁻¹).indicator f) s :=
    MellinConvergent.indicator_source hf _ measurableSet_Iio
  have hwindow :
      MellinConvergent ((sourceWindow lambda).indicator f) s :=
    MellinConvergent.indicator_source hf _ measurableSet_Icc
  have hupper :
      MellinConvergent ((Set.Ioi lambda).indicator f) s :=
    MellinConvergent.indicator_source hf _ measurableSet_Ioi
  unfold mellin lowerMellinTail windowedMellin upperMellinTail
  simp only [mellin]
  rw [← MeasureTheory.integral_add hlower hwindow]
  have hcombine :
      (∫ a : ℝ in Set.Ioi 0,
          (a : ℂ) ^ (s - 1) • (Set.Iio lambda⁻¹).indicator f a +
            (a : ℂ) ^ (s - 1) • (sourceWindow lambda).indicator f a) +
        ∫ a : ℝ in Set.Ioi 0,
          (a : ℂ) ^ (s - 1) • (Set.Ioi lambda).indicator f a =
        ∫ a : ℝ in Set.Ioi 0,
          ((a : ℂ) ^ (s - 1) • (Set.Iio lambda⁻¹).indicator f a +
            (a : ℂ) ^ (s - 1) • (sourceWindow lambda).indicator f a) +
              (a : ℂ) ^ (s - 1) • (Set.Ioi lambda).indicator f a := by
    exact (MeasureTheory.integral_add (hlower.add hwindow) hupper).symm
  rw [hcombine]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hlambda0 : 0 < lambda := zero_lt_one.trans_le hlambda
  have hlambda_inv : 0 < lambda⁻¹ := inv_pos.mpr hlambda0
  have hinv_le : lambda⁻¹ ≤ lambda :=
    (inv_le_one_of_one_le₀ hlambda).trans hlambda
  by_cases hlo : u < lambda⁻¹
  · have hnotwin : u ∉ sourceWindow lambda := by
      intro huw
      exact (not_le_of_gt hlo) huw.1
    have hnotupper : u ∉ Set.Ioi lambda := by
      intro huu
      exact (not_lt_of_ge hinv_le) (huu.trans hlo)
    have hlo_mem : u ∈ Set.Iio lambda⁻¹ := hlo
    rw [Set.indicator_of_mem hlo_mem,
      Set.indicator_of_notMem hnotwin,
      Set.indicator_of_notMem hnotupper]
    simp
  · have hlowle : lambda⁻¹ ≤ u := le_of_not_gt hlo
    by_cases hhi : u ≤ lambda
    · have hwin : u ∈ sourceWindow lambda := ⟨hlowle, hhi⟩
      have hnotlower : u ∉ Set.Iio lambda⁻¹ := not_lt.mpr hlowle
      have hnotupper : u ∉ Set.Ioi lambda := not_lt.mpr hhi
      rw [Set.indicator_of_notMem hnotlower,
        Set.indicator_of_mem hwin,
        Set.indicator_of_notMem hnotupper]
      simp
    · have hupp : u ∈ Set.Ioi lambda := lt_of_not_ge hhi
      have hnotlower : u ∉ Set.Iio lambda⁻¹ := not_lt.mpr hlowle
      have hnotwindow : u ∉ sourceWindow lambda := by
        intro huw
        exact hhi huw.2
      rw [Set.indicator_of_notMem hnotlower,
        Set.indicator_of_notMem hnotwindow,
        Set.indicator_of_mem hupp]
      simp

/-- T2 in the absolute-convergence region.

The absolute-region algebra does not use `hmass`: the proof locks and clears
it.  The hypothesis remains explicit only because zero mass is the guard
needed by the future continuation into the critical strip.  Consequently the
name `zeroMass_decomposition_abs` is stronger than the minimal absolute-domain
contract.  No continuation is claimed here. -/
theorem windowedMellin_E_star_zeroMass_decomposition_abs
    {lambda : ℝ} (hlambda : 1 ≤ lambda)
    {h : ℝ → ℂ} {s : ℂ}
    (hmass : ZeroPositiveMass h)
    (hp : 1 < (s + 1 / 2).re)
    (habs : EStarMellinAbsolute h (s + 1 / 2))
    (hEconv : MellinConvergent (E_star h) s) :
    windowedMellin lambda (E_star h) s =
      riemannZeta (s + 1 / 2) * mellin h (s + 1 / 2) -
        lowerMellinTail lambda (E_star h) s -
          upperMellinTail lambda (E_star h) s := by
  have hmass_locked : ZeroPositiveMass h := hmass
  clear hmass_locked
  have hsplit :=
    mellin_eq_lower_add_window_add_upper hlambda hEconv
  rw [mellin_E_star_eq_riemannZeta_mul hp habs] at hsplit
  calc
    windowedMellin lambda (E_star h) s =
        (lowerMellinTail lambda (E_star h) s +
            windowedMellin lambda (E_star h) s +
              upperMellinTail lambda (E_star h) s) -
          lowerMellinTail lambda (E_star h) s -
            upperMellinTail lambda (E_star h) s := by ring
    _ = riemannZeta (s + 1 / 2) * mellin h (s + 1 / 2) -
          lowerMellinTail lambda (E_star h) s -
            upperMellinTail lambda (E_star h) s := by rw [← hsplit]

theorem nonzeroMassPlant_nonnegative (v : ℝ) :
    0 ≤ nonzeroMassPlant v := by
  unfold nonzeroMassPlant
  by_cases hv : v ∈ Set.Ioc (0 : ℝ) 1 <;> simp [hv]

theorem nonzeroMassPlant_positiveMass :
    (∫ v : ℝ in Set.Ioi 0, nonzeroMassPlant v) = 1 := by
  unfold nonzeroMassPlant
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc]
  have hinter :
      Set.Ioi (0 : ℝ) ∩ Set.Ioc 0 1 = Set.Ioc 0 1 :=
    Set.inter_eq_right.mpr Set.Ioc_subset_Ioi_self
  rw [hinter]
  simp

theorem nonzeroMassPlant_not_zeroMass :
    ¬ ZeroPositiveMass (fun v => (nonzeroMassPlant v : ℂ)) := by
  unfold ZeroPositiveMass
  have hcast :
      (∫ v : ℝ in Set.Ioi 0, (nonzeroMassPlant v : ℂ)) =
        Complex.ofReal
          (∫ v : ℝ in Set.Ioi 0, nonzeroMassPlant v) := by
    exact
      integral_ofReal
        (X := ℝ) (μ := volume.restrict (Set.Ioi 0))
        (𝕜 := ℂ) (f := nonzeroMassPlant)
  rw [hcast, nonzeroMassPlant_positiveMass]
  norm_num

theorem poleRatioModel_eq_J_ratio
    {lambda sigma : ℝ} (hlambda : 1 < lambda) (hsigma : 0 ≤ sigma) :
    poleRatioModel lambda sigma =
      poleWindowJReal lambda (-sigma) / poleWindowJReal lambda 0 := by
  have hlambda0 : 0 < lambda := zero_lt_one.trans hlambda
  have hhalf : (lambda ^ (1 / 2 : ℝ)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hlambda0 _)
  have hsden : (1 + 2 * sigma) ≠ 0 := by linarith
  have hden : (1 - lambda⁻¹) ≠ 0 := by
    have hinv_lt : lambda⁻¹ < 1 := (inv_lt_one₀ hlambda0).mpr hlambda
    linarith
  have hnum :
      lambda ^ (1 / 2 + sigma) - lambda ^ (-sigma - 1 / 2) =
        lambda ^ (1 / 2 + sigma) *
          (1 - lambda ^ (-1 - 2 * sigma)) := by
    rw [mul_sub, mul_one, ← Real.rpow_add hlambda0]
    congr 2
    ring
  have hdenfac :
      lambda ^ (1 / 2 : ℝ) - lambda ^ (-1 / 2 : ℝ) =
        lambda ^ (1 / 2 : ℝ) * (1 - lambda⁻¹) := by
    rw [mul_sub, mul_one]
    rw [← Real.rpow_neg_one]
    rw [← Real.rpow_add hlambda0]
    congr 2
    ring
  have hpow :
      lambda ^ (1 / 2 + sigma) =
        lambda ^ (1 / 2 : ℝ) * lambda ^ sigma := by
    rw [← Real.rpow_add hlambda0]
  unfold poleRatioModel poleWindowJReal
  norm_num only [neg_neg, sub_neg_eq_add, sub_zero]
  have hnegHalf : (-(1 / 2) : ℝ) = -1 / 2 := by ring
  rw [hnegHalf]
  rw [hnum, hdenfac, hpow]
  field_simp [hhalf, hsden, hden]

theorem poleRatioModel_lower
    {lambda sigma : ℝ} (hlambda : 1 < lambda) (hsigma : 0 ≤ sigma) :
    lambda ^ sigma / (1 + 2 * sigma) ≤ poleRatioModel lambda sigma := by
  have hlambda0 : 0 < lambda := zero_lt_one.trans hlambda
  have hlambda1 : 1 ≤ lambda := hlambda.le
  have hpow :
      lambda ^ (-1 - 2 * sigma) ≤ lambda ^ (-1 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hlambda1
    linarith
  have hinv : lambda ^ (-1 : ℝ) = lambda⁻¹ := by
    rw [Real.rpow_neg_one]
  have hden : 0 < 1 - lambda⁻¹ := by
    have hinv_lt : lambda⁻¹ < 1 := (inv_lt_one₀ hlambda0).mpr hlambda
    linarith
  have hfrac :
      1 ≤ (1 - lambda ^ (-1 - 2 * sigma)) / (1 - lambda⁻¹) := by
    rw [le_div_iff₀ hden]
    rw [one_mul]
    rw [← hinv] at hden ⊢
    linarith
  have hbase :
      0 ≤ lambda ^ sigma / (1 + 2 * sigma) := by positivity
  unfold poleRatioModel
  exact le_mul_of_one_le_right hbase hfrac

/-- The pole plant's factor has an explicit lower bound proportional to
`lambda^sigma`; in particular a uniformly bounded implementation has dropped
the nonzero-mass counterterm.  This is not a T2 regularity-class plant. -/
theorem nonzeroMassPlant_pole_growth
    {lambda sigma : ℝ} (hlambda : 1 < lambda) (hsigma : 0 ≤ sigma) :
    lambda ^ sigma / (1 + 2 * sigma) ≤
      (1 : ℝ) * poleRatioModel lambda sigma := by
  simpa using poleRatioModel_lower hlambda hsigma

#print axioms E_star_eq_finiteEStar_of_windowFiniteSupport
#print axioms indicator_scaledSourceWindow_comp
#print axioms mem_scaledSourceWindow_iff
#print axioms dirichletWindow_eq_constraint_sum
#print axioms mellin_windowed_scaled
#print axioms mellinConvergent_windowed_scaled_iff
#print axioms windowedMellin_finiteEStarCore_eq_sum
#print axioms windowedMellin_finiteEStarCore_eq_dirichlet_sum
#print axioms finiteEStar_eq_cpow_mul_core
#print axioms windowedMellin_finiteEStar_eq_shift
#print axioms mul_dirichletWindow_eq_indicator_sum
#print axioms weightedDirichletWindowIntegral_eq_sum
#print axioms windowedMellin_finiteEStar_eq_weightedDirichletWindowIntegral
#print axioms windowedMellin_E_star_eq_finiteEStar
#print axioms windowedMellin_E_star_eq_weightedDirichletWindowIntegral
#print axioms E_star_eq_cpow_smul_eStarCore
#print axioms mellin_E_star_eq_shifted_core
#print axioms mellin_eStarCore_eq_tsum
#print axioms pnatDirichletSeries_eq_riemannZeta
#print axioms mellin_E_star_eq_riemannZeta_mul
#print axioms MellinConvergent.indicator_source
#print axioms mellin_eq_lower_add_window_add_upper
#print axioms windowedMellin_E_star_zeroMass_decomposition_abs
#print axioms nonzeroMassPlant_nonnegative
#print axioms nonzeroMassPlant_positiveMass
#print axioms nonzeroMassPlant_not_zeroMass
#print axioms poleRatioModel_eq_J_ratio
#print axioms poleRatioModel_lower
#print axioms nonzeroMassPlant_pole_growth

end Q3.RouteB.D0Pstar
