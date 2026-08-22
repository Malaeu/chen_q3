import Mathlib
import RequestProject.Defs


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open Set Filter Topology MeasureTheory

/-! ## Milestone 1: the Lagrange/Green identity with the degenerate coefficient `1 - x^2` -/

/-- **Lagrange identity.** If `(f, f1, f2)` solves the spheroidal equation with parameter `Λf`
and `(g, g1, g2)` solves it with parameter `Λg`, then the Wronskian-type expression
`(1 - x^2) (f' g - f g')` has derivative `(Λg - Λf) f g` at every interior point. -/
theorem spheroidal_lagrange_identity (G Lf Lg : ℝ) (f f1 f2 g g1 g2 : ℝ → ℝ)
    (hfd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x)
    (hgd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt g (g1 x) x ∧ HasDerivAt g1 (g2 x) x)
    (hfe : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Lf + G) * f x)
    (hge : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * g2 x + 2 * x * g1 x + G * x ^ 2 * g x = (Lg + G) * g x)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t : ℝ => (1 - t ^ 2) * (f1 t * g t - f t * g1 t))
      ((Lg - Lf) * (f x * g x)) x := by
  obtain ⟨hf, hf'⟩ := hfd x hx
  obtain ⟨hg, hg'⟩ := hgd x hx
  have hpoly : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_sub 1)
  have H := hpoly.mul ((hf'.mul hg).sub (hf.mul hg'))
  simp only [Pi.mul_apply, Pi.sub_apply] at H
  convert H using 1
  have e1 := hfe x hx
  have e2 := hge x hx
  linear_combination g x * e1 - f x * e2

/-- **Energy identity.** With `E x = -(1 - x^2) f'(x) f(x)`, one has
`E' x = (Λ + G (1 - x^2)) f(x)^2 - (1 - x^2) f'(x)^2`. -/
theorem spheroidal_energy_identity (G Λ : ℝ) (f f1 f2 : ℝ → ℝ)
    (hfd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x)
    (hfe : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Λ + G) * f x)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t : ℝ => -((1 - t ^ 2) * (f1 t * f t)))
      ((Λ + G * (1 - x ^ 2)) * f x ^ 2 - (1 - x ^ 2) * f1 x ^ 2) x := by
  obtain ⟨hf, hf'⟩ := hfd x hx
  have hpoly : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_sub 1)
  have H := (hpoly.mul (hf'.mul hf)).neg
  simp only [Pi.mul_apply] at H
  convert H using 1
  have e1 := hfe x hx
  linear_combination (-(f x)) * e1

/-- The open interval is a neighbourhood of `1` inside `(-∞, 1)`. -/
theorem Ioo_mem_nhdsWithin_Iio_one : Ioo (-1 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := by
  rw [show Ioo (-1 : ℝ) 1 = Iio 1 ∩ Ioi (-1) by ext y; simp [and_comm]]
  exact inter_mem_nhdsWithin _ (Ioi_mem_nhds (by norm_num))

/-- The open interval is a neighbourhood of `-1` inside `(-1, ∞)`. -/
theorem Ioo_mem_nhdsWithin_Ioi_negOne : Ioo (-1 : ℝ) 1 ∈ 𝓝[>] (-1 : ℝ) :=
  inter_mem_nhdsWithin _ (Iio_mem_nhds (by norm_num))

/-- Approaching `1` from the left is approaching it from within `[-1,1]`. -/
theorem nhdsWithin_Iio_one_le_Icc : 𝓝[<] (1 : ℝ) ≤ 𝓝[Icc (-1 : ℝ) 1] 1 :=
  nhdsWithin_le_iff.mpr (mem_of_superset Ioo_mem_nhdsWithin_Iio_one Ioo_subset_Icc_self)

/-- Approaching `-1` from the right is approaching it from within `[-1,1]`. -/
theorem nhdsWithin_Ioi_negOne_le_Icc : 𝓝[>] (-1 : ℝ) ≤ 𝓝[Icc (-1 : ℝ) 1] (-1) :=
  nhdsWithin_le_iff.mpr (mem_of_superset Ioo_mem_nhdsWithin_Ioi_negOne Ioo_subset_Icc_self)

/-- The Wronskian of two regular eigenfunctions tends to `0` at the right endpoint. -/
theorem spheroidal_wronskian_tendsto_one (f f1 g g1 : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) (hg : ContinuousOn g (Icc (-1 : ℝ) 1))
    (hf1 : Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[<] (1 : ℝ)) (𝓝 0))
    (hg1 : Tendsto (fun x : ℝ => (1 - x ^ 2) * g1 x) (𝓝[<] (1 : ℝ)) (𝓝 0)) :
    Tendsto (fun x : ℝ => (1 - x ^ 2) * (f1 x * g x - f x * g1 x)) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hgc : Tendsto g (𝓝[<] (1 : ℝ)) (𝓝 (g 1)) :=
    (hg.continuousWithinAt (by norm_num)).mono_left nhdsWithin_Iio_one_le_Icc
  have hfc : Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 (f 1)) :=
    (hf.continuousWithinAt (by norm_num)).mono_left nhdsWithin_Iio_one_le_Icc
  have key := (hf1.mul hgc).sub (hfc.mul hg1)
  have h := key.congr (f₂ := fun x : ℝ => (1 - x ^ 2) * (f1 x * g x - f x * g1 x))
    (fun x => by ring)
  simpa using h

/-- The Wronskian of two regular eigenfunctions tends to `0` at the left endpoint. -/
theorem spheroidal_wronskian_tendsto_neg_one (f f1 g g1 : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) (hg : ContinuousOn g (Icc (-1 : ℝ) 1))
    (hf1 : Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[>] (-1 : ℝ)) (𝓝 0))
    (hg1 : Tendsto (fun x : ℝ => (1 - x ^ 2) * g1 x) (𝓝[>] (-1 : ℝ)) (𝓝 0)) :
    Tendsto (fun x : ℝ => (1 - x ^ 2) * (f1 x * g x - f x * g1 x)) (𝓝[>] (-1 : ℝ)) (𝓝 0) := by
  have hgc : Tendsto g (𝓝[>] (-1 : ℝ)) (𝓝 (g (-1))) :=
    (hg.continuousWithinAt (by norm_num)).mono_left nhdsWithin_Ioi_negOne_le_Icc
  have hfc : Tendsto f (𝓝[>] (-1 : ℝ)) (𝓝 (f (-1))) :=
    (hf.continuousWithinAt (by norm_num)).mono_left nhdsWithin_Ioi_negOne_le_Icc
  have key := (hf1.mul hgc).sub (hfc.mul hg1)
  have h := key.congr (f₂ := fun x : ℝ => (1 - x ^ 2) * (f1 x * g x - f x * g1 x))
    (fun x => by ring)
  simpa using h

/-! ## Milestone 2: one-dimensionality of the regular even eigenspace -/

/-- Lipschitz bound for the first-order system attached to the spheroidal equation on a
compactly contained subinterval `(-c, c)` of `(-1,1)`. -/
theorem spheroidal_field_lipschitzOnWith (G Λ c : ℝ) (hc1 : c < 1) (hcsq : 0 < 1 - c ^ 2)
    (L : ℝ) (hLdef : L = (2 + |G| + |Λ + G|) / (1 - c ^ 2) + 1) (hL0 : 0 ≤ L)
    (t : ℝ) (ht : t ∈ Ioo (-c) c) :
    LipschitzOnWith ⟨L, hL0⟩
      (fun p : ℝ × ℝ => (p.2, (2 * t * p.2 + (G * t ^ 2 - (Λ + G)) * p.1) / (1 - t ^ 2)))
      univ := by
  set M : ℝ := 2 + |G| + |Λ + G| with hM
  have hM0 : 0 ≤ M := by positivity
  have htabs : |t| < c := abs_lt.mpr ⟨ht.1, ht.2⟩
  have ht1 : |t| ≤ 1 := le_of_lt (lt_trans htabs hc1)
  have htsq : 1 - c ^ 2 ≤ 1 - t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
  have htpos : 0 < 1 - t ^ 2 := lt_of_lt_of_le hcsq htsq
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have : 0 ≤ M / (1 - c ^ 2) := by positivity
    linarith
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro p _ q _
  rw [Prod.dist_eq, Prod.dist_eq]
  simp only [NNReal.coe_mk]
  set d := max (dist p.1 q.1) (dist p.2 q.2) with hdd
  have hd1 : |p.1 - q.1| ≤ d := by rw [← Real.dist_eq]; exact le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ d := by rw [← Real.dist_eq]; exact le_max_right _ _
  have hd0 : 0 ≤ d := le_trans (abs_nonneg _) hd1
  refine max_le ?_ ?_
  · calc dist p.2 q.2 ≤ d := le_max_right _ _
      _ ≤ L * d := by nlinarith
  · simp only [Real.dist_eq]
    rw [div_sub_div_same, abs_div, abs_of_pos htpos, div_le_iff₀ htpos]
    have e : 2 * t * p.2 + (G * t ^ 2 - (Λ + G)) * p.1 -
        (2 * t * q.2 + (G * t ^ 2 - (Λ + G)) * q.1)
        = 2 * t * (p.2 - q.2) + (G * t ^ 2 - (Λ + G)) * (p.1 - q.1) := by ring
    rw [e]
    have b1 : |2 * t * (p.2 - q.2)| ≤ 2 * d := by
      rw [abs_mul]
      have h2t : |2 * t| ≤ 2 := by rw [abs_mul]; simp; linarith
      exact mul_le_mul h2t hd2 (abs_nonneg _) (by norm_num)
    have hcoef : |G * t ^ 2 - (Λ + G)| ≤ |G| + |Λ + G| := by
      have h1 : |G * t ^ 2 - (Λ + G)| ≤ |G * t ^ 2| + |Λ + G| := by
        rw [sub_eq_add_neg]
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_neg]
      have h2 : |G * t ^ 2| ≤ |G| := by
        rw [abs_mul, abs_pow]
        nlinarith [abs_nonneg G, abs_nonneg t,
          mul_nonneg (abs_nonneg G)
            (mul_nonneg (sub_nonneg.mpr ht1) (by positivity : (0:ℝ) ≤ 1 + |t|))]
      linarith
    have b2 : |(G * t ^ 2 - (Λ + G)) * (p.1 - q.1)| ≤ (|G| + |Λ + G|) * d := by
      rw [abs_mul]
      exact mul_le_mul hcoef hd1 (abs_nonneg _) (by positivity)
    have btot : |2 * t * (p.2 - q.2) + (G * t ^ 2 - (Λ + G)) * (p.1 - q.1)| ≤ M * d := by
      calc |2 * t * (p.2 - q.2) + (G * t ^ 2 - (Λ + G)) * (p.1 - q.1)|
          ≤ |2 * t * (p.2 - q.2)| + |(G * t ^ 2 - (Λ + G)) * (p.1 - q.1)| := abs_add_le _ _
        _ ≤ 2 * d + (|G| + |Λ + G|) * d := by linarith
        _ = M * d := by rw [hM]; ring
    have hstep : M * d ≤ L * d * (1 - t ^ 2) := by
      have hLc : L * (1 - c ^ 2) = M + (1 - c ^ 2) := by rw [hLdef]; field_simp
      have h1 : L * d * (1 - c ^ 2) = M * d + (1 - c ^ 2) * d := by
        have h3 : L * d * (1 - c ^ 2) = (L * (1 - c ^ 2)) * d := by ring
        rw [h3, hLc]; ring
      have h2 : L * d * (1 - c ^ 2) ≤ L * d * (1 - t ^ 2) :=
        mul_le_mul_of_nonneg_left htsq (by positivity)
      nlinarith
    linarith

/-- Uniqueness for the initial value problem at `x = 0`, in the phase plane. -/
theorem spheroidal_ivp_unique_pair (G Λ : ℝ) (f f1 f2 g g1 g2 : ℝ → ℝ)
    (hfd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x)
    (hgd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt g (g1 x) x ∧ HasDerivAt g1 (g2 x) x)
    (hfe : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Λ + G) * f x)
    (hge : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * g2 x + 2 * x * g1 x + G * x ^ 2 * g x = (Λ + G) * g x)
    (h0 : f 0 = g 0) (h1 : f1 0 = g1 0) :
    EqOn (fun t => (f t, f1 t)) (fun t => (g t, g1 t)) (Ioo (-1 : ℝ) 1) := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  have habs : |x| < 1 := abs_lt.mpr ⟨hx1, hx2⟩
  have habs0 : 0 ≤ |x| := abs_nonneg x
  set c : ℝ := (|x| + 1) / 2 with hcdef
  have hxc : |x| < c := by rw [hcdef]; linarith
  have hc1 : c < 1 := by rw [hcdef]; linarith
  have hc0 : 0 < c := lt_of_le_of_lt habs0 hxc
  have hcsq : 0 < 1 - c ^ 2 := by nlinarith
  set L : ℝ := (2 + |G| + |Λ + G|) / (1 - c ^ 2) + 1 with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hsub : Ioo (-c) c ⊆ Ioo (-1 : ℝ) 1 := Ioo_subset_Ioo (by linarith) (by linarith)
  have hne : ∀ t ∈ Ioo (-c) c, (1 : ℝ) - t ^ 2 ≠ 0 := by
    intro t ht
    have htabs : |t| < c := abs_lt.mpr ⟨ht.1, ht.2⟩
    nlinarith [sq_abs t, abs_nonneg t]
  have key : EqOn (fun t => (f t, f1 t)) (fun t => (g t, g1 t)) (Ioo (-c) c) := by
    refine ODE_solution_unique_of_mem_Ioo
      (v := fun t p => (p.2, (2 * t * p.2 + (G * t ^ 2 - (Λ + G)) * p.1) / (1 - t ^ 2)))
      (s := fun _ => univ) (K := ⟨L, hL0⟩)
      (fun t ht => spheroidal_field_lipschitzOnWith G Λ c hc1 hcsq L hLdef hL0 t ht)
      ⟨by linarith, hc0⟩ ?_ ?_ (by simp [h0, h1])
    · intro t ht
      refine ⟨?_, mem_univ _⟩
      have hd := hfd t (hsub ht)
      have hde : HasDerivAt (fun s => (f s, f1 s)) (f1 t, f2 t) t := hd.1.prodMk hd.2
      convert hde using 1
      have hodd := hfe t (hsub ht)
      have hnz := hne t ht
      simp only [Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      field_simp
      linarith
    · intro t ht
      refine ⟨?_, mem_univ _⟩
      have hd := hgd t (hsub ht)
      have hde : HasDerivAt (fun s => (g s, g1 s)) (g1 t, g2 t) t := hd.1.prodMk hd.2
      convert hde using 1
      have hodd := hge t (hsub ht)
      have hnz := hne t ht
      simp only [Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      field_simp
      linarith
  exact key (abs_lt.mp hxc)

/-- Uniqueness for the initial value problem at `x = 0` on the whole open interval. -/
theorem spheroidal_ivp_unique (G Λ : ℝ) (f f1 f2 g g1 g2 : ℝ → ℝ)
    (hfd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x)
    (hgd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt g (g1 x) x ∧ HasDerivAt g1 (g2 x) x)
    (hfe : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Λ + G) * f x)
    (hge : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * g2 x + 2 * x * g1 x + G * x ^ 2 * g x = (Λ + G) * g x)
    (h0 : f 0 = g 0) (h1 : f1 0 = g1 0) :
    EqOn f g (Ioo (-1 : ℝ) 1) := fun _ hx =>
  congrArg Prod.fst (spheroidal_ivp_unique_pair G Λ f f1 f2 g g1 g2 hfd hgd hfe hge h0 h1 hx)

/-- An even differentiable function has vanishing derivative at `0`. -/
theorem deriv_zero_of_even {f f1 : ℝ → ℝ} (hev : ∀ x : ℝ, f (-x) = f x)
    (hd : HasDerivAt f (f1 0) 0) : f1 0 = 0 := by
  have hn : HasDerivAt (fun x : ℝ => -x) (-1) (0 : ℝ) := hasDerivAt_neg 0
  have hd0 : HasDerivAt f (f1 0) ((fun x : ℝ => -x) 0) := by simpa using hd
  have hcomp : HasDerivAt (fun x : ℝ => f (-x)) (f1 0 * (-1)) 0 := HasDerivAt.comp 0 hd0 hn
  have hf : HasDerivAt f (f1 0 * (-1)) 0 := by
    have hfun : (fun x : ℝ => f (-x)) = f := funext hev
    rwa [hfun] at hcomp
  have := hd.unique hf
  linarith

/-- A solution to the spheroidal equation which is even and vanishes at the origin vanishes
identically on `(-1,1)`. -/
theorem spheroidal_eq_zero_of_center_zero (G Λ : ℝ) (f f1 f2 : ℝ → ℝ)
    (hfev : ∀ x : ℝ, f (-x) = f x)
    (hfd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x)
    (hfe : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Λ + G) * f x)
    (h0 : f 0 = 0) : EqOn f 0 (Ioo (-1 : ℝ) 1) := by
  have hzero : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
  have h1 : f1 0 = 0 := deriv_zero_of_even hfev (hfd 0 hzero).1
  refine spheroidal_ivp_unique G Λ f f1 f2 0 0 0 hfd
    (fun x _ => ⟨hasDerivAt_const _ _, hasDerivAt_const _ _⟩) hfe (fun x _ => by simp)
    (by simpa using h0) (by simpa using h1)

/-- A nontrivial regular even solution does not vanish at the origin. -/
theorem spheroidal_center_ne_zero (G Λ : ℝ) (f f1 f2 : ℝ → ℝ)
    (hfne : ∃ x ∈ Icc (-1 : ℝ) 1, f x ≠ 0) (hfc : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hfev : ∀ x : ℝ, f (-x) = f x)
    (hfd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x)
    (hfe : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Λ + G) * f x) :
    f 0 ≠ 0 := by
  intro h0
  have hIoo : EqOn f 0 (Ioo (-1 : ℝ) 1) :=
    spheroidal_eq_zero_of_center_zero G Λ f f1 f2 hfev hfd hfe h0
  have hev : f =ᶠ[𝓝[<] (1 : ℝ)] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem Ioo_mem_nhdsWithin_Iio_one (fun y hy => hIoo hy)
  have hone : f 1 = 0 := by
    have hc : Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 (f 1)) :=
      (hfc.continuousWithinAt (by norm_num)).mono_left nhdsWithin_Iio_one_le_Icc
    have hz : Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 0) :=
      Filter.Tendsto.congr' hev.symm tendsto_const_nhds
    exact tendsto_nhds_unique hc hz
  have hnegone : f (-1) = 0 := by rw [hfev 1]; exact hone
  obtain ⟨x, hx, hfx⟩ := hfne
  rcases eq_or_lt_of_le hx.1 with h | h
  · exact hfx (by rw [← h]; exact hnegone)
  · rcases eq_or_lt_of_le hx.2 with h' | h'
    · exact hfx (by rw [h']; exact hone)
    · exact hfx (hIoo ⟨h, h'⟩)

/-- **One-dimensionality of the regular even eigenspace.** If `f` is a nontrivial even solution
of the spheroidal equation which is continuous on `[-1,1]`, then every even solution `g` for the
same eigenvalue is a scalar multiple of `f` on `(-1,1)`. -/
theorem spheroidal_eigenspace_one_dim (G Λ : ℝ) (f f1 f2 g g1 g2 : ℝ → ℝ)
    (hfne : ∃ x ∈ Icc (-1 : ℝ) 1, f x ≠ 0) (hfc : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hfev : ∀ x : ℝ, f (-x) = f x) (hgev : ∀ x : ℝ, g (-x) = g x)
    (hfd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x)
    (hgd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt g (g1 x) x ∧ HasDerivAt g1 (g2 x) x)
    (hfe : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Λ + G) * f x)
    (hge : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * g2 x + 2 * x * g1 x + G * x ^ 2 * g x = (Λ + G) * g x) :
    ∃ c : ℝ, EqOn g (fun x => c * f x) (Ioo (-1 : ℝ) 1) := by
  have hzero : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
  have hf0 : f 0 ≠ 0 := spheroidal_center_ne_zero G Λ f f1 f2 hfne hfc hfev hfd hfe
  refine ⟨g 0 / f 0, ?_⟩
  have hg1 : g1 0 = 0 := deriv_zero_of_even hgev (hgd 0 hzero).1
  have hf1 : f1 0 = 0 := deriv_zero_of_even hfev (hfd 0 hzero).1
  refine spheroidal_ivp_unique G Λ g g1 g2 (fun x => g 0 / f 0 * f x)
    (fun x => g 0 / f 0 * f1 x) (fun x => g 0 / f 0 * f2 x) hgd
    (fun x hx => ⟨((hfd x hx).1).const_mul _, ((hfd x hx).2).const_mul _⟩) hge
    (fun x hx => by linear_combination (g 0 / f 0) * hfe x hx) ?_ ?_
  · field_simp
  · simp [hg1, hf1]

/-- **Orthogonality.** Regular even eigenfunctions for distinct eigenvalues are orthogonal in
`L²(-1,1)`. This is the Green identity integrated up to the endpoints. -/
theorem spheroidal_orthogonality (G Lf Lg : ℝ) (f f1 f2 g g1 g2 : ℝ → ℝ) (hne : Lf ≠ Lg)
    (hfc : ContinuousOn f (Icc (-1 : ℝ) 1)) (hgc : ContinuousOn g (Icc (-1 : ℝ) 1))
    (hfd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x)
    (hgd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt g (g1 x) x ∧ HasDerivAt g1 (g2 x) x)
    (hfe : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Lf + G) * f x)
    (hge : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * g2 x + 2 * x * g1 x + G * x ^ 2 * g x = (Lg + G) * g x)
    (hfr : Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[<] (1 : ℝ)) (𝓝 0))
    (hfl : Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[>] (-1 : ℝ)) (𝓝 0))
    (hgr : Tendsto (fun x : ℝ => (1 - x ^ 2) * g1 x) (𝓝[<] (1 : ℝ)) (𝓝 0))
    (hgl : Tendsto (fun x : ℝ => (1 - x ^ 2) * g1 x) (𝓝[>] (-1 : ℝ)) (𝓝 0)) :
    ∫ x in (-1 : ℝ)..1, f x * g x = 0 := by
  set W : ℝ → ℝ := fun t => (1 - t ^ 2) * (f1 t * g t - f t * g1 t) with hW
  have hWr : Tendsto W (𝓝[<] (1 : ℝ)) (𝓝 0) :=
    spheroidal_wronskian_tendsto_one f f1 g g1 hfc hgc hfr hgr
  have hWl : Tendsto W (𝓝[>] (-1 : ℝ)) (𝓝 0) :=
    spheroidal_wronskian_tendsto_neg_one f f1 g g1 hfc hgc hfl hgl
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (-1 : ℝ) 1, |f x * g x| ≤ C := by
    obtain ⟨C, hCb⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      (hfc.mul hgc)
    exact ⟨max C 0, le_max_right _ _, fun x hx =>
      le_trans (by simpa [Real.norm_eq_abs] using hCb x hx) (le_max_left _ _)⟩
  have hint : ∀ a b : ℝ, a ∈ Icc (-1 : ℝ) 1 → b ∈ Icc (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => f x * g x) volume a b := by
    intro a b ha hb
    exact ContinuousOn.intervalIntegrable
      ((hfc.mul hgc).mono ((Set.ordConnected_Icc).uIcc_subset ha hb))
  set I := ∫ x in (-1 : ℝ)..1, f x * g x with hI
  have hFTC : ∀ a b : ℝ, a ∈ Ioo (-1 : ℝ) 1 → b ∈ Ioo (-1 : ℝ) 1 →
      (Lg - Lf) * (∫ x in a..b, f x * g x) = W b - W a := by
    intro a b ha hb
    have hsub : uIcc a b ⊆ Ioo (-1 : ℝ) 1 := (Set.ordConnected_Ioo).uIcc_subset ha hb
    have hintc : IntervalIntegrable (fun x => (Lg - Lf) * (f x * g x)) volume a b :=
      ((hint a b (Ioo_subset_Icc_self ha) (Ioo_subset_Icc_self hb)).const_mul _)
    have hEq := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := W) (f' := fun x => (Lg - Lf) * (f x * g x))
      (fun x hx => spheroidal_lagrange_identity G Lf Lg f f1 f2 g g1 g2 hfd hgd hfe hge (hsub hx))
      hintc
    rw [intervalIntegral.integral_const_mul] at hEq
    exact hEq
  have hkey : ∀ ε : ℝ, 0 < ε → |(Lg - Lf) * I| ≤ ε := by
    intro ε hε
    set D := |Lg - Lf| * C + 1 with hD
    have hD0 : 0 < D := by positivity
    set δ := ε / (4 * D) with hδ
    have hδ0 : 0 < δ := by positivity
    obtain ⟨b, hbmem, hbW⟩ : ∃ b ∈ Ioo (max 0 (1 - δ)) 1, |W b| < ε / 4 := by
      have h1 : Ioo (max 0 (1 - δ)) 1 ∈ 𝓝[<] (1 : ℝ) :=
        Ioo_mem_nhdsLT (max_lt (by norm_num) (by linarith))
      have h2 : {x : ℝ | |W x| < ε / 4} ∈ 𝓝[<] (1 : ℝ) := by
        have hball := hWr (Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < ε / 4))
        filter_upwards [hball] with x hx
        simpa [Real.dist_eq] using hx
      obtain ⟨b, hb⟩ := Filter.nonempty_of_mem (inter_mem h1 h2)
      exact ⟨b, hb.1, hb.2⟩
    obtain ⟨a, hamem, haW⟩ : ∃ a ∈ Ioo (-1 : ℝ) (min 0 (-1 + δ)), |W a| < ε / 4 := by
      have h1 : Ioo (-1 : ℝ) (min 0 (-1 + δ)) ∈ 𝓝[>] (-1 : ℝ) :=
        Ioo_mem_nhdsGT (lt_min (by norm_num) (by linarith))
      have h2 : {x : ℝ | |W x| < ε / 4} ∈ 𝓝[>] (-1 : ℝ) := by
        have hball := hWl (Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < ε / 4))
        filter_upwards [hball] with x hx
        simpa [Real.dist_eq] using hx
      obtain ⟨a, ha⟩ := Filter.nonempty_of_mem (inter_mem h1 h2)
      exact ⟨a, ha.1, ha.2⟩
    have hb1 : b < 1 := hbmem.2
    have hb0 : 0 ≤ b := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hbmem.1)
    have hbδ : 1 - δ < b := lt_of_le_of_lt (le_max_right _ _) hbmem.1
    have ha1 : -1 < a := hamem.1
    have ha0 : a ≤ 0 := le_of_lt (lt_of_lt_of_le hamem.2 (min_le_left _ _))
    have haδ : a < -1 + δ := lt_of_lt_of_le hamem.2 (min_le_right _ _)
    have haI : a ∈ Ioo (-1 : ℝ) 1 := ⟨ha1, by linarith⟩
    have hbI : b ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hb1⟩
    have hs1 : (∫ x in (-1 : ℝ)..a, f x * g x) + (∫ x in a..b, f x * g x)
        + (∫ x in b..(1 : ℝ), f x * g x) = I := by
      rw [intervalIntegral.integral_add_adjacent_intervals
        (hint (-1) a (by norm_num) (Ioo_subset_Icc_self haI))
        (hint a b (Ioo_subset_Icc_self haI) (Ioo_subset_Icc_self hbI)),
        intervalIntegral.integral_add_adjacent_intervals
        (hint (-1) b (by norm_num) (Ioo_subset_Icc_self hbI))
        (hint b 1 (Ioo_subset_Icc_self hbI) (by norm_num))]
    have hbnd1 : |∫ x in (-1 : ℝ)..a, f x * g x| ≤ C * |a - (-1)| := by
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
        (C := C) (f := fun x => f x * g x) (a := (-1 : ℝ)) (b := a) ?_
      · simpa [Real.norm_eq_abs] using hnorm
      · intro x hx
        rw [uIoc_of_le (by linarith : (-1 : ℝ) ≤ a)] at hx
        simpa [Real.norm_eq_abs] using hC x ⟨le_of_lt hx.1, by linarith [hx.2]⟩
    have hbnd2 : |∫ x in b..(1 : ℝ), f x * g x| ≤ C * |1 - b| := by
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
        (C := C) (f := fun x => f x * g x) (a := b) (b := (1 : ℝ)) ?_
      · simpa [Real.norm_eq_abs] using hnorm
      · intro x hx
        rw [uIoc_of_le (by linarith : b ≤ (1 : ℝ))] at hx
        simpa [Real.norm_eq_abs] using hC x ⟨by linarith [hx.1], hx.2⟩
    have hmid := hFTC a b haI hbI
    have hfinal : |(Lg - Lf) * I|
        ≤ |Lg - Lf| * (C * |a - (-1)| + C * |1 - b|) + (|W b| + |W a|) := by
      have hIexp : (Lg - Lf) * I = (Lg - Lf) * ((∫ x in (-1 : ℝ)..a, f x * g x)
          + (∫ x in b..(1 : ℝ), f x * g x)) + (W b - W a) := by
        rw [← hmid, ← hs1]; ring
      rw [hIexp]
      calc |(Lg - Lf) * ((∫ x in (-1 : ℝ)..a, f x * g x) + (∫ x in b..(1 : ℝ), f x * g x))
            + (W b - W a)|
          ≤ |(Lg - Lf) * ((∫ x in (-1 : ℝ)..a, f x * g x) + (∫ x in b..(1 : ℝ), f x * g x))|
            + |W b - W a| := abs_add_le _ _
        _ ≤ |Lg - Lf| * (C * |a - (-1)| + C * |1 - b|) + (|W b| + |W a|) := by
            gcongr
            · rw [abs_mul]
              gcongr
              exact le_trans (abs_add_le _ _) (by linarith [hbnd1, hbnd2])
            · exact abs_sub _ _
    have hab : |a - (-1)| ≤ δ := by rw [abs_of_nonneg (by linarith)]; linarith
    have hbb : |1 - b| ≤ δ := by rw [abs_of_nonneg (by linarith)]; linarith
    have hCbound : |Lg - Lf| * (C * |a - (-1)| + C * |1 - b|) ≤ ε / 2 := by
      have h1 : C * |a - (-1)| + C * |1 - b| ≤ 2 * C * δ := by
        nlinarith [abs_nonneg (a - (-1)), abs_nonneg (1 - b)]
      have h2 : |Lg - Lf| * (C * |a - (-1)| + C * |1 - b|) ≤ |Lg - Lf| * (2 * C * δ) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      have h3 : |Lg - Lf| * (2 * C * δ) ≤ 2 * D * δ := by
        have hDD : |Lg - Lf| * C ≤ D := by rw [hD]; linarith
        nlinarith [hδ0.le, abs_nonneg (Lg - Lf), hC0]
      have h4 : 2 * D * δ = ε / 2 := by rw [hδ]; field_simp; ring
      linarith
    linarith [hbW, haW]
  by_contra hcon
  have hne' : (Lg - Lf) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have habs : 0 < |(Lg - Lf) * I| := abs_pos.mpr (mul_ne_zero hne' hcon)
  have hhalf := hkey (|(Lg - Lf) * I| / 2) (by linarith)
  linarith

/-! ## A lower bound for the spectrum -/

/-- Every regular even spheroidal eigenvalue is at least `-max G 0`. This is the Green/energy
identity integrated over `(-1,1)`, using the vanishing of the flux at both endpoints. -/
theorem spheroidal_eigenvalue_lower_bound {G Λ : ℝ} (h : RegularEvenSpheroidalEigenvalue G Λ) :
    -max G 0 ≤ Λ := by
  obtain ⟨f, f1, f2, hne, hev, hc, hd, hode, hlim1, hlim2⟩ := h
  have hf0 : f 0 ≠ 0 := spheroidal_center_ne_zero G Λ f f1 f2 hne hc hev hd hode
  by_contra hcon
  push_neg at hcon
  set M := max G 0 with hM
  have hM0 : (0 : ℝ) ≤ M := le_max_right _ _
  have hMG : ∀ x : ℝ, x ∈ Ioo (-1 : ℝ) 1 → G * (1 - x ^ 2) ≤ M := by
    intro x hx
    have h1 : (0 : ℝ) ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    rcases le_total 0 G with hG | hG
    · calc G * (1 - x ^ 2) ≤ G * 1 := by nlinarith [hx.1, hx.2]
        _ = G := by ring
        _ ≤ M := le_max_left _ _
    · calc G * (1 - x ^ 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hG h1
        _ ≤ M := hM0
  have hsum : Λ + M < 0 := by linarith
  have hsubu : ∀ a b : ℝ, a ∈ Ioo (-1 : ℝ) 1 → b ∈ Ioo (-1 : ℝ) 1 → uIcc a b ⊆ Ioo (-1 : ℝ) 1 :=
    fun a b ha hb => (Set.ordConnected_Ioo).uIcc_subset ha hb
  have hsubi : ∀ a b : ℝ, a ∈ Ioo (-1 : ℝ) 1 → b ∈ Ioo (-1 : ℝ) 1 → Icc a b ⊆ Ioo (-1 : ℝ) 1 :=
    fun a b ha hb => (Set.ordConnected_Ioo).out ha hb
  have hint1 : ∀ a b : ℝ, a ∈ Ioo (-1 : ℝ) 1 → b ∈ Ioo (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => (Λ + G * (1 - x ^ 2)) * f x ^ 2 - (1 - x ^ 2) * f1 x ^ 2)
        volume a b := by
    intro a b ha hb
    refine ContinuousOn.intervalIntegrable (fun x hx => ?_)
    have hx' := hsubu a b ha hb hx
    have h1 : ContinuousAt f x := (hd x hx').1.continuousAt
    have h2 : ContinuousAt f1 x := (hd x hx').2.continuousAt
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hint2 : ∀ a b : ℝ, a ∈ Ioo (-1 : ℝ) 1 → b ∈ Ioo (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => (Λ + G * (1 - x ^ 2)) * f x ^ 2) volume a b := by
    intro a b ha hb
    refine ContinuousOn.intervalIntegrable (fun x hx => ?_)
    have hx' := hsubu a b ha hb hx
    have h1 : ContinuousAt f x := (hd x hx').1.continuousAt
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hint3 : ∀ a b : ℝ, a ∈ Ioo (-1 : ℝ) 1 → b ∈ Ioo (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => (1 - x ^ 2) * f1 x ^ 2) volume a b := by
    intro a b ha hb
    refine ContinuousOn.intervalIntegrable (fun x hx => ?_)
    have hx' := hsubu a b ha hb hx
    have h2 : ContinuousAt f1 x := (hd x hx').2.continuousAt
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hint4 : ∀ a b : ℝ, a ∈ Ioo (-1 : ℝ) 1 → b ∈ Ioo (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => (Λ + M) * f x ^ 2) volume a b := by
    intro a b ha hb
    refine ContinuousOn.intervalIntegrable (fun x hx => ?_)
    have hx' := hsubu a b ha hb hx
    have h1 : ContinuousAt f x := (hd x hx').1.continuousAt
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hint5 : ∀ a b : ℝ, a ∈ Ioo (-1 : ℝ) 1 → b ∈ Ioo (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => f x ^ 2) volume a b := by
    intro a b ha hb
    refine ContinuousOn.intervalIntegrable (fun x hx => ?_)
    have hx' := hsubu a b ha hb hx
    have h1 : ContinuousAt f x := (hd x hx').1.continuousAt
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hzero : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
  have hfc0 : ContinuousAt f 0 := (hd 0 hzero).1.continuousAt
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp (hfc0.eventually_ne hf0)
  set r := min (δ / 2) (1 / 2) with hr
  have hr0 : 0 < r := lt_min (by linarith) (by norm_num)
  have hr1 : r < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hrm : (-r) ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hrp : r ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hr1⟩
  set c := ∫ x in (-r)..r, f x ^ 2 with hcdef
  have hcpos : 0 < c := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hint5 _ _ hrm hrp) (fun x hx => ?_)
      (by linarith)
    have hxa : |x| < r := abs_lt.mpr ⟨hx.1, hx.2⟩
    have hfx : f x ≠ 0 := by
      refine hδ ?_
      rw [Real.dist_eq, sub_zero]
      calc |x| < r := hxa
        _ ≤ δ / 2 := min_le_left _ _
        _ < δ := by linarith
    positivity
  set E : ℝ → ℝ := fun t => -((1 - t ^ 2) * (f1 t * f t)) with hE
  have hFTC : ∀ a b : ℝ, a ∈ Ioo (-1 : ℝ) 1 → b ∈ Ioo (-1 : ℝ) 1 →
      (∫ x in a..b, ((Λ + G * (1 - x ^ 2)) * f x ^ 2 - (1 - x ^ 2) * f1 x ^ 2)) = E b - E a := by
    intro a b ha hb
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) (hint1 a b ha hb)
    exact spheroidal_energy_identity G Λ f f1 f2 hd hode (hsubu a b ha hb hx)
  have hkey : ∀ a b : ℝ, a ∈ Ioo (-1 : ℝ) (-r) → b ∈ Ioo r 1 → E b - E a ≤ (Λ + M) * c := by
    intro a b ha hb
    have ha' : a ∈ Ioo (-1 : ℝ) 1 := ⟨ha.1, by linarith [ha.2]⟩
    have hb' : b ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hb.1], hb.2⟩
    have hab : a ≤ b := by linarith [ha.2, hb.1]
    rw [← hFTC a b ha' hb',
      intervalIntegral.integral_sub (hint2 a b ha' hb') (hint3 a b ha' hb')]
    have hQ : 0 ≤ ∫ x in a..b, (1 - x ^ 2) * f1 x ^ 2 := by
      refine intervalIntegral.integral_nonneg hab (fun x hx => ?_)
      have hx' : x ∈ Ioo (-1 : ℝ) 1 := hsubi a b ha' hb' hx
      have h1 : (0 : ℝ) ≤ 1 - x ^ 2 := by nlinarith [hx'.1, hx'.2]
      positivity
    have hP : (∫ x in a..b, (Λ + G * (1 - x ^ 2)) * f x ^ 2) ≤ ∫ x in a..b, (Λ + M) * f x ^ 2 := by
      refine intervalIntegral.integral_mono_on hab (hint2 a b ha' hb') (hint4 a b ha' hb')
        (fun x hx => ?_)
      have hx' : x ∈ Ioo (-1 : ℝ) 1 := hsubi a b ha' hb' hx
      have hle := hMG x hx'
      nlinarith [sq_nonneg (f x)]
    have hconst : (∫ x in a..b, (Λ + M) * f x ^ 2) = (Λ + M) * ∫ x in a..b, f x ^ 2 :=
      intervalIntegral.integral_const_mul _ _
    have hmono : c ≤ ∫ x in a..b, f x ^ 2 := by
      refine intervalIntegral.integral_mono_interval (by linarith [ha.2]) (by linarith)
        (by linarith [hb.1]) ?_ (hint5 a b ha' hb')
      exact Filter.Eventually.of_forall (fun x => sq_nonneg (f x))
    have hfin : (Λ + M) * (∫ x in a..b, f x ^ 2) ≤ (Λ + M) * c :=
      mul_le_mul_of_nonpos_left hmono hsum.le
    linarith [hP, hQ, hconst ▸ hfin]
  have hEright : Tendsto E (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hfl : Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 (f 1)) :=
      (hc.continuousWithinAt (by norm_num)).mono_left nhdsWithin_Iio_one_le_Icc
    have h := (hlim1.mul hfl).neg
    refine Tendsto.congr' ?_ (by simpa using h)
    filter_upwards with x
    simp only [hE]
    ring
  have hEleft : Tendsto E (𝓝[>] (-1 : ℝ)) (𝓝 0) := by
    have hfl : Tendsto f (𝓝[>] (-1 : ℝ)) (𝓝 (f (-1))) :=
      (hc.continuousWithinAt (by norm_num)).mono_left nhdsWithin_Ioi_negOne_le_Icc
    have h := (hlim2.mul hfl).neg
    refine Tendsto.congr' ?_ (by simpa using h)
    filter_upwards with x
    simp only [hE]
    ring
  set ε := -((Λ + M) * c) / 2 with hεdef
  have hεpos : 0 < ε := by
    have hneg : (Λ + M) * c < 0 := mul_neg_of_neg_of_pos hsum hcpos
    simp only [hεdef]
    linarith
  obtain ⟨b, hbmem, hbE⟩ : ∃ b ∈ Ioo r 1, |E b| < ε / 2 := by
    have h1 : Ioo r 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT hr1
    have h2 : {x : ℝ | |E x| < ε / 2} ∈ 𝓝[<] (1 : ℝ) := by
      have hball := hEright (Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < ε / 2))
      filter_upwards [hball] with x hx
      simpa [Real.dist_eq] using hx
    obtain ⟨b, hb⟩ := Filter.nonempty_of_mem (inter_mem h1 h2)
    exact ⟨b, hb.1, hb.2⟩
  obtain ⟨a, hamem, haE⟩ : ∃ a ∈ Ioo (-1 : ℝ) (-r), |E a| < ε / 2 := by
    have h1 : Ioo (-1 : ℝ) (-r) ∈ 𝓝[>] (-1 : ℝ) := Ioo_mem_nhdsGT (by linarith)
    have h2 : {x : ℝ | |E x| < ε / 2} ∈ 𝓝[>] (-1 : ℝ) := by
      have hball := hEleft (Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < ε / 2))
      filter_upwards [hball] with x hx
      simpa [Real.dist_eq] using hx
    obtain ⟨a, ha⟩ := Filter.nonempty_of_mem (inter_mem h1 h2)
    exact ⟨a, ha.1, ha.2⟩
  have hbound := hkey a b hamem hbmem
  have h1 := abs_lt.mp hbE
  have h2 := abs_lt.mp haE
  simp only [hεdef] at h1 h2
  linarith [h1.1, h2.2]

/-! ## The logarithmically singular even solution at `G = 0`, `Λ = 2` -/

/-- The even Legendre function of the second kind of degree one (up to sign and normalisation):
`qLeg x = 1 - (x/2) * log((1+x)/(1-x))`. It solves the Legendre equation with `Λ = 2` and is
even, but its flux does not vanish at the endpoints. -/
noncomputable def qLeg (x : ℝ) : ℝ := 1 - x / 2 * (Real.log (1 + x) - Real.log (1 - x))

/-- The derivative of `qLeg`. -/
noncomputable def qLeg1 (x : ℝ) : ℝ :=
  -(1 / 2) * (Real.log (1 + x) - Real.log (1 - x)) - x / (1 - x ^ 2)

/-- The second derivative of `qLeg`. -/
noncomputable def qLeg2 (x : ℝ) : ℝ := -1 / (1 - x ^ 2) - (1 + x ^ 2) / (1 - x ^ 2) ^ 2

theorem qLeg_hasDerivAt {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : HasDerivAt qLeg (qLeg1 x) x := by
  have hp : (0 : ℝ) < 1 + x := by linarith [hx.1]
  have hm : (0 : ℝ) < 1 - x := by linarith [hx.2]
  have hsq : (1 : ℝ) - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by simpa using (hasDerivAt_id x).const_add 1
  have h2 : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by simpa using (hasDerivAt_id x).const_sub 1
  have hlog1 : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + x)) x := by
    have h := (Real.hasDerivAt_log (ne_of_gt hp)).comp x h1
    simpa [one_div] using h
  have hlog2 : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-(1 / (1 - x))) x := by
    have h := (Real.hasDerivAt_log (ne_of_gt hm)).comp x h2
    simpa [one_div] using h
  have hl := hlog1.sub hlog2
  have hxd : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) x := by
    simpa using (hasDerivAt_id x).div_const 2
  have H := (hxd.mul hl).const_sub 1
  simp only [Pi.sub_apply] at H
  convert H using 1
  simp only [qLeg1]
  field_simp
  ring

theorem qLeg1_hasDerivAt {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : HasDerivAt qLeg1 (qLeg2 x) x := by
  have hp : (0 : ℝ) < 1 + x := by linarith [hx.1]
  have hm : (0 : ℝ) < 1 - x := by linarith [hx.2]
  have hsq : (1 : ℝ) - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by simpa using (hasDerivAt_id x).const_add 1
  have h2 : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by simpa using (hasDerivAt_id x).const_sub 1
  have hlog1 : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + x)) x := by
    have h := (Real.hasDerivAt_log (ne_of_gt hp)).comp x h1
    simpa [one_div] using h
  have hlog2 : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-(1 / (1 - x))) x := by
    have h := (Real.hasDerivAt_log (ne_of_gt hm)).comp x h2
    simpa [one_div] using h
  have hl := (hlog1.sub hlog2).const_mul (-(1 / 2) : ℝ)
  have hden : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_sub 1)
  have hfrac : HasDerivAt (fun t : ℝ => t / (1 - t ^ 2))
      ((1 * (1 - x ^ 2) - x * (-(2 * x))) / (1 - x ^ 2) ^ 2) x := (hasDerivAt_id x).div hden hsq
  have H := hl.sub hfrac
  simp only [Pi.sub_apply] at H
  convert H using 1
  simp only [qLeg2]
  field_simp
  ring

theorem qLeg_ode {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    -(1 - x ^ 2) * qLeg2 x + 2 * x * qLeg1 x + 0 * x ^ 2 * qLeg x = (2 + 0) * qLeg x := by
  have hsq : (1 : ℝ) - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  simp only [qLeg, qLeg1, qLeg2]
  field_simp
  ring

theorem qLeg_even (x : ℝ) : qLeg (-x) = qLeg x := by
  simp only [qLeg]
  ring_nf

theorem qLeg_zero : qLeg 0 = 1 := by simp [qLeg]

theorem qLeg1_zero : qLeg1 0 = 0 := by simp [qLeg1]

/-- `(1-x) log (1-x) → 0` as `x → 1⁻`. -/
theorem tendsto_one_sub_mul_log :
    Tendsto (fun x : ℝ => (1 - x) * Real.log (1 - x)) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hmap : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun x : ℝ => 1 - x) (𝓝 (1 : ℝ)) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      simpa using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx1 : x < 1 := hx
      simp only [mem_Ioi]
      linarith
  have h := (tendsto_log_mul_rpow_nhdsGT_zero (r := 1) one_pos).comp hmap
  refine h.congr ?_
  intro x
  simp [Real.rpow_one, mul_comm]

/-- The flux of the logarithmically singular solution tends to `-1`, not `0`. -/
theorem qLeg1_flux_limit :
    Tendsto (fun x : ℝ => (1 - x ^ 2) * qLeg1 x) (𝓝[<] (1 : ℝ)) (𝓝 (-1)) := by
  have hlog1 : Tendsto (fun x : ℝ => -(1 / 2) * ((1 - x ^ 2) * Real.log (1 + x))) (𝓝[<] (1 : ℝ))
      (𝓝 (-(1 / 2) * ((1 - 1 ^ 2) * Real.log (1 + 1)))) := by
    have hc : ContinuousAt (fun x : ℝ => -(1 / 2) * ((1 - x ^ 2) * Real.log (1 + x))) 1 := by
      apply ContinuousAt.mul continuousAt_const
      exact (by fun_prop : ContinuousAt (fun x : ℝ => 1 - x ^ 2) 1).mul
        ((Real.continuousAt_log (by norm_num)).comp (by fun_prop))
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hlog2 : Tendsto (fun x : ℝ => (1 / 2) * ((1 + x) * ((1 - x) * Real.log (1 - x))))
      (𝓝[<] (1 : ℝ)) (𝓝 ((1 / 2) * (2 * 0))) := by
    refine Tendsto.const_mul _ (Tendsto.mul ?_ tendsto_one_sub_mul_log)
    have hcont : Continuous (fun x : ℝ => 1 + x) := by fun_prop
    have h := hcont.tendsto (1 : ℝ)
    norm_num at h
    exact h.mono_left nhdsWithin_le_nhds
  have hx : Tendsto (fun x : ℝ => -x) (𝓝[<] (1 : ℝ)) (𝓝 (-1)) :=
    (continuous_neg.tendsto 1).mono_left nhdsWithin_le_nhds
  have hsum := (hlog1.add hlog2).add hx
  norm_num at hsum
  refine Tendsto.congr' ?_ hsum
  filter_upwards [Ioo_mem_nhdsWithin_Iio_one] with x hx'
  have h1 : -1 < x := hx'.1
  have h2 : x < 1 := hx'.2
  have hsq : (1 : ℝ) - x ^ 2 ≠ 0 := by nlinarith
  simp only [qLeg1]
  field_simp
  ring

/-! ## Mandatory semantic controls at `G = 0` -/

/-- At `G = 0`, the constant function `1` is an even regular eigenfunction with `Λ = 0`. -/
theorem control_zero_mem : RegularEvenSpheroidalEigenvalue 0 0 := by
  refine ⟨fun _ => 1, fun _ => 0, fun _ => 0, ⟨0, by norm_num, by norm_num⟩, fun _ => rfl,
    continuousOn_const, fun x _ => ⟨hasDerivAt_const _ _, hasDerivAt_const _ _⟩,
    fun x _ => by ring, by simp, by simp⟩

/-- At `G = 0`, `(3 x^2 - 1)/2` is an even regular eigenfunction with `Λ = 6`. -/
theorem control_six_mem : RegularEvenSpheroidalEigenvalue 0 6 := by
  refine ⟨fun x => (3 * x ^ 2 - 1) / 2, fun x => 3 * x, fun _ => 3,
    ⟨1, by norm_num, by norm_num⟩, fun x => by ring, by fun_prop, fun x _ => ⟨?_, ?_⟩,
    fun x _ => by ring, ?_, ?_⟩
  · have h := (((hasDerivAt_pow 2 x).const_mul 3).sub_const 1).div_const 2
    convert h using 1
    push_cast
    ring
  · simpa using (hasDerivAt_id x).const_mul 3
  · have hc : Continuous (fun x : ℝ => (1 - x ^ 2) * (3 * x)) := by fun_prop
    have h := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
    simpa using h
  · have hc : Continuous (fun x : ℝ => (1 - x ^ 2) * (3 * x)) := by fun_prop
    have h := (hc.tendsto (-1)).mono_left (nhdsWithin_le_nhds (s := Ioi (-1 : ℝ)))
    simpa using h

/-- At `G = 0`, `Λ = 2` is *not* an even regular eigenvalue: the eigenfunction `x` is odd, and
the even solution at `Λ = 2` is the logarithmically singular Legendre function of the second
kind, which violates the endpoint condition. -/
theorem control_two_not_mem : ¬ RegularEvenSpheroidalEigenvalue 0 2 := by
  rintro ⟨f, f1, f2, hne, hev, hc, hd, hode, hlim1, -⟩
  have hzero : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
  have hf0 : f 0 ≠ 0 := spheroidal_center_ne_zero 0 2 f f1 f2 hne hc hev hd hode
  have hf10 : f1 0 = 0 := deriv_zero_of_even hev (hd 0 hzero).1
  have hpair := spheroidal_ivp_unique_pair 0 2 f f1 f2 (fun x => f 0 * qLeg x)
    (fun x => f 0 * qLeg1 x) (fun x => f 0 * qLeg2 x) hd
    (fun x hx => ⟨(qLeg_hasDerivAt hx).const_mul _, (qLeg1_hasDerivAt hx).const_mul _⟩) hode
    (fun x hx => by linear_combination f 0 * qLeg_ode hx)
    (by simp [qLeg_zero]) (by simp [hf10, qLeg1_zero])
  have heq1 : ∀ x ∈ Ioo (-1 : ℝ) 1, f1 x = f 0 * qLeg1 x := fun x hx =>
    congrArg Prod.snd (hpair hx)
  have hlim : Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[<] (1 : ℝ)) (𝓝 (f 0 * (-1))) := by
    refine Tendsto.congr' ?_ (qLeg1_flux_limit.const_mul (f 0))
    filter_upwards [Ioo_mem_nhdsWithin_Iio_one] with x hx
    rw [heq1 x hx]
    ring
  have hzeroeq := tendsto_nhds_unique hlim1 hlim
  exact hf0 (by linarith)

/-- The companion to the previous control: at `G = 0` the function `x` *is* a regular solution
with `Λ = 2` (with vanishing endpoint flux), but it is odd, so it does not enter the even
spectrum. -/
theorem control_two_odd_witness :
    (∀ x ∈ Ioo (-1 : ℝ) 1,
        HasDerivAt (fun t : ℝ => t) (1 : ℝ) x ∧ HasDerivAt (fun _ : ℝ => (1 : ℝ)) (0 : ℝ) x) ∧
      (∀ x ∈ Ioo (-1 : ℝ) 1, -(1 - x ^ 2) * 0 + 2 * x * 1 + 0 * x ^ 2 * x = (2 + 0) * x) ∧
      Tendsto (fun x : ℝ => (1 - x ^ 2) * 1) (𝓝[<] (1 : ℝ)) (𝓝 0) ∧
      Tendsto (fun x : ℝ => (1 - x ^ 2) * 1) (𝓝[>] (-1 : ℝ)) (𝓝 0) ∧
      ¬ (∀ x : ℝ, (fun t : ℝ => t) (-x) = (fun t : ℝ => t) x) := by
  refine ⟨fun x _ => ⟨hasDerivAt_id x, hasDerivAt_const _ _⟩, fun x _ => by ring, ?_, ?_, ?_⟩
  · have hcont : Continuous (fun x : ℝ => (1 - x ^ 2) * 1) := by fun_prop
    have h := (hcont.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
    simpa using h
  · have hcont : Continuous (fun x : ℝ => (1 - x ^ 2) * 1) := by fun_prop
    have h := (hcont.tendsto (-1)).mono_left (nhdsWithin_le_nhds (s := Ioi (-1 : ℝ)))
    simpa using h
  · intro hcon
    have := hcon 1
    norm_num at this

/-! ## Milestone 4: enumerating a discrete, bounded below, infinite set of reals -/

/-- A set of reals which is infinite and meets every half-line `(-∞, b]` in a finite set is the
range of a strictly monotone sequence. -/
theorem exists_strictMono_range_eq_of_locallyFinite {S : Set ℝ}
    (hinf : S.Infinite) (hlf : ∀ b : ℝ, (S ∩ Iic b).Finite) :
    ∃ μ : ℕ → ℝ, StrictMono μ ∧ range μ = S := by
  classical
  have hfinIio : ∀ s : ℝ, (S ∩ Iio s).Finite :=
    fun s => (hlf s).subset (fun x hx => ⟨hx.1, le_of_lt (mem_Iio.mp hx.2)⟩)
  have hleast : ∀ T : Set ℝ, T ⊆ S → T.Nonempty → ∃ m, IsLeast T m := by
    intro T hTS hT
    obtain ⟨t, ht⟩ := hT
    have hfin : (T ∩ Iic t).Finite := (hlf t).subset (fun x hx => ⟨hTS hx.1, hx.2⟩)
    have hne : (T ∩ Iic t).Nonempty := ⟨t, ht, le_refl t⟩
    have hFne : hfin.toFinset.Nonempty := by rwa [Set.Finite.toFinset_nonempty]
    refine ⟨hfin.toFinset.min' hFne, ?_, ?_⟩
    · have hm := hfin.toFinset.min'_mem hFne
      rw [Set.Finite.mem_toFinset] at hm
      exact hm.1
    · intro y hy
      rcases le_total y t with h | h
      · exact hfin.toFinset.min'_le y (by rw [Set.Finite.mem_toFinset]; exact ⟨hy, h⟩)
      · have hm := hfin.toFinset.min'_mem hFne
        rw [Set.Finite.mem_toFinset] at hm
        exact le_trans hm.2 h
  obtain ⟨m0, hm0⟩ := hleast S (le_refl S) hinf.nonempty
  have hnext : ∀ t : ℝ, ∃ m, IsLeast (S ∩ Ioi t) m := by
    intro t
    refine hleast _ (fun x hx => hx.1) ?_
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hsub : S ⊆ S ∩ Iic t := by
      intro x hx
      rcases le_or_gt x t with h | h
      · exact ⟨hx, h⟩
      · exact absurd (Set.mem_inter hx (mem_Ioi.mpr h)) (by rw [hcon]; exact fun hmem => hmem)
    exact hinf ((hlf t).subset hsub)
  choose next hnextspec using hnext
  set μ : ℕ → ℝ := fun n => Nat.rec m0 (fun _ prev => next prev) n with hμ
  have hμ0 : μ 0 = m0 := rfl
  have hμsucc : ∀ n, μ (n + 1) = next (μ n) := fun n => rfl
  have hmemS : ∀ n, μ n ∈ S := by
    intro n
    induction n with
    | zero => exact hm0.1
    | succ k ih => rw [hμsucc]; exact (hnextspec (μ k)).1.1
  have hmono : StrictMono μ := by
    refine strictMono_nat_of_lt_succ (fun n => ?_)
    rw [hμsucc]
    exact (hnextspec (μ n)).1.2
  refine ⟨μ, hmono, ?_⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨n, rfl⟩
    exact hmemS n
  · intro s hs
    have key : ∀ n : ℕ, ∀ s ∈ S, (S ∩ Iio s).ncard = n → ∃ k, μ k = s := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro s hs hcard
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn
          have hempty : S ∩ Iio s = ∅ := by
            rwa [Set.ncard_eq_zero (hfinIio s)] at hcard
          refine ⟨0, ?_⟩
          rw [hμ0]
          have h1 : m0 ≤ s := hm0.2 hs
          rcases lt_or_eq_of_le h1 with h | h
          · exact absurd (Set.mem_inter hm0.1 (mem_Iio.mpr h)) (by rw [hempty]; exact fun hm => hm)
          · exact h
        · have hfin := hfinIio s
          have hne : (S ∩ Iio s).Nonempty := by
            refine Set.nonempty_of_ncard_ne_zero ?_
            omega
          have hFne : hfin.toFinset.Nonempty := by rwa [Set.Finite.toFinset_nonempty]
          set t := hfin.toFinset.max' hFne with ht
          have htmem : t ∈ S ∩ Iio s := by
            have hm := hfin.toFinset.max'_mem hFne
            rwa [Set.Finite.mem_toFinset] at hm
          have htmax : ∀ y ∈ S ∩ Iio s, y ≤ t := by
            intro y hy
            exact hfin.toFinset.le_max' y (by rwa [Set.Finite.mem_toFinset])
          have hsubset : S ∩ Iio t ⊆ S ∩ Iio s :=
            fun x hx => ⟨hx.1, lt_trans (mem_Iio.mp hx.2) (mem_Iio.mp htmem.2)⟩
          have hssubset : S ∩ Iio t ⊂ S ∩ Iio s := by
            refine ⟨hsubset, ?_⟩
            intro hcon
            have hmem := hcon htmem
            exact absurd (mem_Iio.mp hmem.2) (lt_irrefl t)
          have hlt : (S ∩ Iio t).ncard < n := by
            rw [← hcard]
            exact Set.ncard_lt_ncard hssubset (hfinIio s)
          obtain ⟨k, hk⟩ := ih _ hlt t htmem.1 rfl
          refine ⟨k + 1, ?_⟩
          rw [hμsucc, hk]
          have hle : next t ≤ s := (hnextspec t).2 ⟨hs, mem_Ioi.mpr (mem_Iio.mp htmem.2)⟩
          have hgt : t < next t := (hnextspec t).1.2
          rcases lt_or_eq_of_le hle with h | h
          · have hcontra : next t ≤ t := htmax _ ⟨(hnextspec t).1.1, mem_Iio.mpr h⟩
            linarith
          · exact h
    exact key _ s hs rfl

/-! ## Uniform energy and tail estimates for eigenfunctions

The estimates in this section are uniform over the family of all regular even eigenfunctions
with eigenvalue below a fixed bound; they are the quantitative input for discreteness. -/

/-- **Dirichlet energy bound.** For a regular even eigenfunction, the weighted Dirichlet energy
`∫ (1 - x²) f'(x)²` over any interior interval is at most `(Λ + |G|) ∫_{-1}^{1} f²`. -/
theorem spheroidal_dirichlet_energy_bound (G Λ : ℝ) (f f1 f2 : ℝ → ℝ)
    (hK : 0 ≤ Λ + |G|)
    (hc : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x)
    (hode : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Λ + G) * f x)
    (hlim1 : Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[<] (1 : ℝ)) (𝓝 0))
    (hlim2 : Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[>] (-1 : ℝ)) (𝓝 0))
    {a b : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1) (hb : b ∈ Ioo (-1 : ℝ) 1) (hab : a ≤ b) :
    (∫ x in a..b, (1 - x ^ 2) * f1 x ^ 2) ≤ (Λ + |G|) * ∫ x in (-1 : ℝ)..1, f x ^ 2 := by
  have hsubu : ∀ u v : ℝ, u ∈ Ioo (-1 : ℝ) 1 → v ∈ Ioo (-1 : ℝ) 1 → uIcc u v ⊆ Ioo (-1 : ℝ) 1 :=
    fun u v hu hv => (Set.ordConnected_Ioo).uIcc_subset hu hv
  have hsubi : ∀ u v : ℝ, u ∈ Ioo (-1 : ℝ) 1 → v ∈ Ioo (-1 : ℝ) 1 → Icc u v ⊆ Ioo (-1 : ℝ) 1 :=
    fun u v hu hv => (Set.ordConnected_Ioo).out hu hv
  have hint1 : ∀ u v : ℝ, u ∈ Ioo (-1 : ℝ) 1 → v ∈ Ioo (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => (Λ + G * (1 - x ^ 2)) * f x ^ 2 - (1 - x ^ 2) * f1 x ^ 2)
        volume u v := by
    intro u v hu hv
    refine ContinuousOn.intervalIntegrable (fun x hx => ?_)
    have hx' := hsubu u v hu hv hx
    have h1 : ContinuousAt f x := (hd x hx').1.continuousAt
    have h2 : ContinuousAt f1 x := (hd x hx').2.continuousAt
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hint2 : ∀ u v : ℝ, u ∈ Ioo (-1 : ℝ) 1 → v ∈ Ioo (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => (Λ + G * (1 - x ^ 2)) * f x ^ 2) volume u v := by
    intro u v hu hv
    refine ContinuousOn.intervalIntegrable (fun x hx => ?_)
    have hx' := hsubu u v hu hv hx
    have h1 : ContinuousAt f x := (hd x hx').1.continuousAt
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hint3 : ∀ u v : ℝ, u ∈ Ioo (-1 : ℝ) 1 → v ∈ Ioo (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => (1 - x ^ 2) * f1 x ^ 2) volume u v := by
    intro u v hu hv
    refine ContinuousOn.intervalIntegrable (fun x hx => ?_)
    have hx' := hsubu u v hu hv hx
    have h2 : ContinuousAt f1 x := (hd x hx').2.continuousAt
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hint4 : ∀ u v : ℝ, u ∈ Ioo (-1 : ℝ) 1 → v ∈ Ioo (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => (Λ + |G|) * f x ^ 2) volume u v := by
    intro u v hu hv
    refine ContinuousOn.intervalIntegrable (fun x hx => ?_)
    have hx' := hsubu u v hu hv hx
    have h1 : ContinuousAt f x := (hd x hx').1.continuousAt
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hintsq : ∀ u v : ℝ, u ∈ Icc (-1 : ℝ) 1 → v ∈ Icc (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => f x ^ 2) volume u v := by
    intro u v hu hv
    exact ContinuousOn.intervalIntegrable
      (((hc.mul hc).mono ((Set.ordConnected_Icc).uIcc_subset hu hv)).congr
        (fun x _ => by simp [Pi.mul_apply, sq]))
  set E : ℝ → ℝ := fun t => -((1 - t ^ 2) * (f1 t * f t)) with hE
  have hFTC : ∀ u v : ℝ, u ∈ Ioo (-1 : ℝ) 1 → v ∈ Ioo (-1 : ℝ) 1 →
      (∫ x in u..v, ((Λ + G * (1 - x ^ 2)) * f x ^ 2 - (1 - x ^ 2) * f1 x ^ 2)) = E v - E u := by
    intro u v hu hv
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) (hint1 u v hu hv)
    exact spheroidal_energy_identity G Λ f f1 f2 hd hode (hsubu u v hu hv hx)
  have hEright : Tendsto E (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hfl : Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 (f 1)) :=
      (hc.continuousWithinAt (by norm_num)).mono_left nhdsWithin_Iio_one_le_Icc
    have h := (hlim1.mul hfl).neg
    refine Tendsto.congr' ?_ (by simpa using h)
    filter_upwards with x
    simp only [hE]
    ring
  have hEleft : Tendsto E (𝓝[>] (-1 : ℝ)) (𝓝 0) := by
    have hfl : Tendsto f (𝓝[>] (-1 : ℝ)) (𝓝 (f (-1))) :=
      (hc.continuousWithinAt (by norm_num)).mono_left nhdsWithin_Ioi_negOne_le_Icc
    have h := (hlim2.mul hfl).neg
    refine Tendsto.congr' ?_ (by simpa using h)
    filter_upwards with x
    simp only [hE]
    ring
  -- the key estimate on a slightly larger interval
  have hkey : ∀ u v : ℝ, u ∈ Ioo (-1 : ℝ) 1 → v ∈ Ioo (-1 : ℝ) 1 → u ≤ a → b ≤ v →
      (∫ x in a..b, (1 - x ^ 2) * f1 x ^ 2)
        ≤ (Λ + |G|) * (∫ x in (-1 : ℝ)..1, f x ^ 2) + (|E v| + |E u|) := by
    intro u v hu hv hua hbv
    have huv : u ≤ v := le_trans hua (le_trans hab hbv)
    have henlarge : (∫ x in a..b, (1 - x ^ 2) * f1 x ^ 2)
        ≤ ∫ x in u..v, (1 - x ^ 2) * f1 x ^ 2 := by
      refine intervalIntegral.integral_mono_interval hua hab hbv ?_ (hint3 u v hu hv)
      have hpos : ∀ x ∈ Ioc u v, 0 ≤ (1 - x ^ 2) * f1 x ^ 2 := by
        intro x hx
        have hx' : x ∈ Ioo (-1 : ℝ) 1 := hsubi u v hu hv ⟨hx.1.le, hx.2⟩
        have h1 : (0 : ℝ) ≤ 1 - x ^ 2 := by nlinarith [hx'.1, hx'.2]
        positivity
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx using hpos x hx
    have hsplit : (∫ x in u..v, (1 - x ^ 2) * f1 x ^ 2)
        = (∫ x in u..v, (Λ + G * (1 - x ^ 2)) * f x ^ 2) - (E v - E u) := by
      rw [← hFTC u v hu hv, intervalIntegral.integral_sub (hint2 u v hu hv) (hint3 u v hu hv)]
      ring
    have hmono1 : (∫ x in u..v, (Λ + G * (1 - x ^ 2)) * f x ^ 2)
        ≤ ∫ x in u..v, (Λ + |G|) * f x ^ 2 := by
      refine intervalIntegral.integral_mono_on huv (hint2 u v hu hv) (hint4 u v hu hv)
        (fun x hx => ?_)
      have hx' : x ∈ Ioo (-1 : ℝ) 1 := hsubi u v hu hv hx
      have h1 : (0 : ℝ) ≤ 1 - x ^ 2 := by nlinarith [hx'.1, hx'.2]
      have h2 : G * (1 - x ^ 2) ≤ |G| := by
        nlinarith [le_abs_self G, neg_abs_le G, abs_nonneg G, hx'.1, hx'.2]
      nlinarith [sq_nonneg (f x)]
    have hconst : (∫ x in u..v, (Λ + |G|) * f x ^ 2) = (Λ + |G|) * ∫ x in u..v, f x ^ 2 :=
      intervalIntegral.integral_const_mul _ _
    have hmono2 : (∫ x in u..v, f x ^ 2) ≤ ∫ x in (-1 : ℝ)..1, f x ^ 2 := by
      refine intervalIntegral.integral_mono_interval (by linarith [hu.1]) huv
        (by linarith [hv.2]) (Filter.Eventually.of_forall (fun x => sq_nonneg (f x)))
        (hintsq (-1) 1 (by norm_num) (by norm_num))
    have hfin : (Λ + |G|) * (∫ x in u..v, f x ^ 2) ≤ (Λ + |G|) * ∫ x in (-1 : ℝ)..1, f x ^ 2 :=
      mul_le_mul_of_nonneg_left hmono2 hK
    have h1 : E v - E u ≥ -(|E v| + |E u|) := by
      have := abs_le.mp (le_refl |E v|)
      have h2 := neg_abs_le (E v)
      have h3 := le_abs_self (E u)
      linarith
    linarith [hconst ▸ hfin]
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨v, hvmem, hvE⟩ : ∃ v ∈ Ioo b 1, |E v| < ε / 2 := by
    have h1 : Ioo b 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT hb.2
    have h2 : {x : ℝ | |E x| < ε / 2} ∈ 𝓝[<] (1 : ℝ) := by
      have hball := hEright (Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < ε / 2))
      filter_upwards [hball] with x hx
      simpa [Real.dist_eq] using hx
    obtain ⟨v, hv⟩ := Filter.nonempty_of_mem (inter_mem h1 h2)
    exact ⟨v, hv.1, hv.2⟩
  obtain ⟨u, humem, huE⟩ : ∃ u ∈ Ioo (-1 : ℝ) a, |E u| < ε / 2 := by
    have h1 : Ioo (-1 : ℝ) a ∈ 𝓝[>] (-1 : ℝ) := Ioo_mem_nhdsGT ha.1
    have h2 : {x : ℝ | |E x| < ε / 2} ∈ 𝓝[>] (-1 : ℝ) := by
      have hball := hEleft (Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < ε / 2))
      filter_upwards [hball] with x hx
      simpa [Real.dist_eq] using hx
    obtain ⟨u, hu⟩ := Filter.nonempty_of_mem (inter_mem h1 h2)
    exact ⟨u, hu.1, hu.2⟩
  have hu' : u ∈ Ioo (-1 : ℝ) 1 := ⟨humem.1, by linarith [humem.2, ha.2]⟩
  have hv' : v ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hvmem.1, hb.1], hvmem.2⟩
  have := hkey u v hu' hv' humem.2.le hvmem.1.le
  linarith
/-- An arithmetic–geometric mean characterisation of the Cauchy–Schwarz bound: if a
nonnegative number `u` satisfies `u ≤ (l * A + B / l) / 2` for every `l > 0`, then `u² ≤ A * B`. -/
theorem real_sq_le_mul_of_forall_amgm {u A B : ℝ} (hu : 0 ≤ u) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ l : ℝ, 0 < l → u ≤ (l * A + B / l) / 2) : u ^ 2 ≤ A * B := by
  rcases eq_or_lt_of_le hA with hA0 | hA0
  · have hu0 : u = 0 := by
      by_contra hne
      have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hne)
      have hl : (0 : ℝ) < B / u + 1 := by positivity
      have hkey := h _ hl
      rw [← hA0] at hkey
      have hBl : B / (B / u + 1) < u := by
        rw [div_lt_iff₀ hl]
        have : B / u * u = B := div_mul_cancel₀ B (ne_of_gt hupos)
        nlinarith [this]
      simp only [mul_zero, zero_add] at hkey
      linarith
    simp [hu0, ← hA0]
  · rcases eq_or_lt_of_le hB with hB0 | hB0
    · have hu0 : u = 0 := by
        by_contra hne
        have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hne)
        have hl : (0 : ℝ) < u / A := by positivity
        have hkey := h _ hl
        rw [← hB0] at hkey
        have hkey2 : u ≤ (u / A * A) / 2 := by simpa using hkey
        rw [div_mul_cancel₀ u (ne_of_gt hA0)] at hkey2
        linarith
      simp [hu0, ← hB0]
    · set s := Real.sqrt (A * B) with hs
      have hs2 : s ^ 2 = A * B := Real.sq_sqrt (by positivity)
      have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
      have hl : (0 : ℝ) < s / A := by positivity
      have hkey := h _ hl
      have h1 : s / A * A = s := div_mul_cancel₀ s (ne_of_gt hA0)
      have h2 : B / (s / A) = s := by
        field_simp
        nlinarith [hs2]
      rw [h1, h2] at hkey
      have hus : u ≤ s := by linarith
      nlinarith [hs2, hu]

/-- **Cauchy–Schwarz for the degenerate weight.** The squared increment of `f` is bounded by the
weighted Dirichlet energy times the integral of the reciprocal weight. -/
theorem spheroidal_sq_sub_le (f f1 : ℝ → ℝ)
    (hd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x)
    (hf1c : ContinuousOn f1 (Ioo (-1 : ℝ) 1))
    {y x : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) (hx : x ∈ Ioo (-1 : ℝ) 1) (hyx : y ≤ x) :
    (f x - f y) ^ 2 ≤ (∫ t in y..x, (1 - t ^ 2) * f1 t ^ 2) * (∫ t in y..x, 1 / (1 - t ^ 2)) := by
  have hsub : uIcc y x ⊆ Ioo (-1 : ℝ) 1 := (Set.ordConnected_Ioo).uIcc_subset hy hx
  have hpos : ∀ t ∈ uIcc y x, (0 : ℝ) < 1 - t ^ 2 := by
    intro t ht
    have h := hsub ht
    nlinarith [h.1, h.2]
  have hc1 : ContinuousOn f1 (uIcc y x) := hf1c.mono hsub
  have hi1 : IntervalIntegrable f1 volume y x := hc1.intervalIntegrable
  have hiabs : IntervalIntegrable (fun t => |f1 t|) volume y x := hi1.abs
  have hiA : IntervalIntegrable (fun t => (1 - t ^ 2) * f1 t ^ 2) volume y x :=
    ContinuousOn.intervalIntegrable
      ((continuousOn_const.sub (continuousOn_pow 2)).mul (hc1.pow 2))
  have hcw : ContinuousOn (fun t : ℝ => 1 / (1 - t ^ 2)) (uIcc y x) := by
    intro t ht
    have hne : (1 - t ^ 2) ≠ 0 := ne_of_gt (hpos t ht)
    have h1 : ContinuousAt (fun t : ℝ => 1 - t ^ 2) t := by fun_prop
    exact (continuousAt_const.div h1 hne).continuousWithinAt
  have hiB : IntervalIntegrable (fun t : ℝ => 1 / (1 - t ^ 2)) volume y x :=
    hcw.intervalIntegrable
  set A := ∫ t in y..x, (1 - t ^ 2) * f1 t ^ 2 with hAdef
  set B := ∫ t in y..x, 1 / (1 - t ^ 2) with hBdef
  set u := ∫ t in y..x, |f1 t| with hudef
  have hA0 : 0 ≤ A := by
    refine intervalIntegral.integral_nonneg hyx (fun t ht => ?_)
    have := hpos t (by rw [uIcc_of_le hyx]; exact ht)
    positivity
  have hB0 : 0 ≤ B := by
    refine intervalIntegral.integral_nonneg hyx (fun t ht => ?_)
    have := hpos t (by rw [uIcc_of_le hyx]; exact ht)
    positivity
  have hu0 : 0 ≤ u := intervalIntegral.integral_nonneg hyx (fun t _ => abs_nonneg _)
  have hkey : ∀ l : ℝ, 0 < l → u ≤ (l * A + B / l) / 2 := by
    intro l hl
    have hmono : u ≤ ∫ t in y..x,
        (l * ((1 - t ^ 2) * f1 t ^ 2) + (1 / l) * (1 / (1 - t ^ 2))) / 2 := by
      refine intervalIntegral.integral_mono_on hyx hiabs ?_ (fun t ht => ?_)
      · exact (((hiA.const_mul l).add (hiB.const_mul (1 / l))).div_const 2)
      · have htm : t ∈ uIcc y x := by rw [uIcc_of_le hyx]; exact ht
        have hp := hpos t htm
        have hsq : f1 t ^ 2 = |f1 t| ^ 2 := (sq_abs _).symm
        rw [hsq, ← sub_nonneg]
        have key : (l * ((1 - t ^ 2) * |f1 t| ^ 2) + 1 / l * (1 / (1 - t ^ 2))) / 2 - |f1 t|
            = (l * (1 - t ^ 2) * |f1 t| - 1) ^ 2 / (2 * l * (1 - t ^ 2)) := by
          field_simp
          ring
        rw [key]
        positivity
    have hval : (∫ t in y..x, (l * ((1 - t ^ 2) * f1 t ^ 2) + (1 / l) * (1 / (1 - t ^ 2))) / 2)
        = (l * A + B / l) / 2 := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hiA.const_mul l)
        (hiB.const_mul (1 / l)), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      rw [← hAdef, ← hBdef]
      field_simp
    linarith [hval ▸ hmono]
  have hfin := real_sq_le_mul_of_forall_amgm hu0 hA0 hB0 hkey
  have hFTC : f x - f y = ∫ t in y..x, f1 t :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (hsub ht)) hi1).symm
  have habs : |f x - f y| ≤ u := by
    rw [hFTC]
    exact intervalIntegral.abs_integral_le_integral_abs hyx
  nlinarith [abs_nonneg (f x - f y), sq_abs (f x - f y), hfin, habs, hu0]

/-- The reciprocal weight has a logarithmic integral on `[y,x] ⊆ [0,1)`. -/
theorem spheroidal_integral_inv_one_sub_sq_le {y x : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hx : x < 1) :
    (∫ t in y..x, 1 / (1 - t ^ 2)) ≤ Real.log (1 - y) - Real.log (1 - x) := by
  have hsub : ∀ t ∈ Icc y x, 0 ≤ t ∧ t < 1 := fun t ht =>
    ⟨le_trans hy ht.1, lt_of_le_of_lt ht.2 hx⟩
  have hcw : ContinuousOn (fun t : ℝ => 1 / (1 - t ^ 2)) (uIcc y x) := by
    rw [uIcc_of_le hyx]
    intro t ht
    obtain ⟨h0, h1⟩ := hsub t ht
    have hne : (1 - t ^ 2) ≠ 0 := by nlinarith
    have hc : ContinuousAt (fun t : ℝ => 1 - t ^ 2) t := by fun_prop
    exact (continuousAt_const.div hc hne).continuousWithinAt
  have hcw2 : ContinuousOn (fun t : ℝ => 1 / (1 - t)) (uIcc y x) := by
    rw [uIcc_of_le hyx]
    intro t ht
    obtain ⟨h0, h1⟩ := hsub t ht
    have hne : (1 - t) ≠ 0 := by linarith
    have hc : ContinuousAt (fun t : ℝ => 1 - t) t := by fun_prop
    exact (continuousAt_const.div hc hne).continuousWithinAt
  have hval : (∫ t in y..x, 1 / (1 - t)) = Real.log (1 - y) - Real.log (1 - x) := by
    have hderiv : ∀ t ∈ uIcc y x, HasDerivAt (fun s : ℝ => -Real.log (1 - s)) (1 / (1 - t)) t := by
      intro t ht
      rw [uIcc_of_le hyx] at ht
      obtain ⟨h0, h1⟩ := hsub t ht
      have hne : (1 - t) ≠ 0 := by linarith
      have h2 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub 1
      have h3 := (Real.hasDerivAt_log hne).comp t h2
      have h4 := h3.neg
      convert h4 using 1
      field_simp
    have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcw2.intervalIntegrable
    rw [hI]
    ring
  rw [← hval]
  refine intervalIntegral.integral_mono_on hyx hcw.intervalIntegrable hcw2.intervalIntegrable
    (fun t ht => ?_)
  obtain ⟨h0, h1⟩ := hsub t ht
  exact one_div_le_one_div_of_le (by linarith) (by nlinarith)

/-- The integral of the reciprocal weight is nonnegative. -/
theorem spheroidal_integral_inv_one_sub_sq_nonneg {y x : ℝ} (hy : -1 < y) (hyx : y ≤ x)
    (hx : x < 1) : 0 ≤ ∫ t in y..x, 1 / (1 - t ^ 2) := by
  refine intervalIntegral.integral_nonneg hyx (fun t ht => ?_)
  have h1 : -1 < t := lt_of_lt_of_le hy ht.1
  have h2 : t < 1 := lt_of_le_of_lt ht.2 hx
  have : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
  positivity

/-- **Uniform tail bound.** If the weighted Dirichlet energy of `f` over every interior interval
is at most `D`, then the mass of `f²` on the endpoint layer `[1-τ, 1]` is at most
`2τ f(1-τ)² + 2Dτ`; in particular it tends to `0` with `τ`, uniformly in the family. -/
theorem spheroidal_tail_bound (f f1 : ℝ → ℝ) (D τ : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 2)
    (hcf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x)
    (hf1c : ContinuousOn f1 (Ioo (-1 : ℝ) 1))
    (hD0 : 0 ≤ D)
    (hD : ∀ u v : ℝ, u ∈ Ioo (-1 : ℝ) 1 → v ∈ Ioo (-1 : ℝ) 1 → u ≤ v →
        (∫ t in u..v, (1 - t ^ 2) * f1 t ^ 2) ≤ D) :
    (∫ x in (1 - τ)..1, f x ^ 2) ≤ 2 * τ * f (1 - τ) ^ 2 + 2 * D * τ := by
  set c := 1 - τ with hcdef
  have hc0 : (0 : ℝ) ≤ c := by rw [hcdef]; linarith
  have hc1 : c < 1 := by rw [hcdef]; linarith
  have hcτ : (1 : ℝ) - c = τ := by rw [hcdef]; ring
  have hcIoo : c ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hc1⟩
  have hisq : ∀ u v : ℝ, u ∈ Icc (-1 : ℝ) 1 → v ∈ Icc (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => f x ^ 2) volume u v := by
    intro u v hu hv
    exact ContinuousOn.intervalIntegrable
      ((hcf.mono ((Set.ordConnected_Icc).uIcc_subset hu hv)).pow 2)
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc (-1 : ℝ) 1, f x ^ 2 ≤ M := by
    obtain ⟨M, hMb⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      (hcf.pow 2)
    refine ⟨max M 0, le_max_right _ _, fun x hx => le_trans ?_ (le_max_left _ _)⟩
    have hb := hMb x hx
    calc f x ^ 2 ≤ |f x ^ 2| := le_abs_self _
      _ ≤ M := by simpa [Real.norm_eq_abs] using hb
  set H : ℝ → ℝ := fun x => (1 - x) * (Real.log (1 - x) - Real.log τ - 1) with hHdef
  have hHderiv : ∀ x : ℝ, x < 1 → HasDerivAt H (Real.log τ - Real.log (1 - x)) x := by
    intro x hx
    have hne : (1 - x) ≠ 0 := ne_of_gt (by linarith)
    have h2 : HasDerivAt (fun s : ℝ => 1 - s) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    have h3 : HasDerivAt (fun s : ℝ => Real.log (1 - s)) (-1 / (1 - x)) x := by
      have h := (Real.hasDerivAt_log hne).comp x h2
      simpa [div_eq_inv_mul] using h
    have h4 := h2.mul ((h3.sub_const (Real.log τ)).sub_const 1)
    convert h4 using 1
    field_simp
    ring
  have hlogcont : ∀ x : ℝ, x < 1 →
      ContinuousAt (fun s : ℝ => Real.log τ - Real.log (1 - s)) x := by
    intro x hx
    have hne : (1 - x) ≠ 0 := ne_of_gt (by linarith)
    have h1 : ContinuousAt (fun s : ℝ => 1 - s) x := by fun_prop
    exact continuousAt_const.sub ((Real.continuousAt_log hne).comp h1)
  have key : ∀ d : ℝ, c ≤ d → d < 1 → (∫ x in c..d, f x ^ 2) ≤ 2 * τ * f c ^ 2 + 2 * D * τ := by
    intro d hcd hd1
    set g : ℝ → ℝ := fun x => 2 * f c ^ 2 + 2 * D * (Real.log τ - Real.log (1 - x)) with hgdef
    have hlc : ContinuousOn (fun x : ℝ => Real.log τ - Real.log (1 - x)) (uIcc c d) := by
      rw [uIcc_of_le hcd]
      intro x hx
      exact (hlogcont x (lt_of_le_of_lt hx.2 hd1)).continuousWithinAt
    have hgc : ContinuousOn g (uIcc c d) := by
      rw [uIcc_of_le hcd]
      intro x hx
      have hx1 : x < 1 := lt_of_le_of_lt hx.2 hd1
      exact (continuousAt_const.add (continuousAt_const.mul (hlogcont x hx1))).continuousWithinAt
    have hmono : (∫ x in c..d, f x ^ 2) ≤ ∫ x in c..d, g x := by
      refine intervalIntegral.integral_mono_on hcd
        (hisq c d ⟨by linarith, hc1.le⟩ ⟨by linarith, hd1.le⟩) hgc.intervalIntegrable
        (fun x hx => ?_)
      have hcx : c ≤ x := hx.1
      have hx1 : x < 1 := lt_of_le_of_lt hx.2 hd1
      have hxIoo : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hx1⟩
      have hA := hD c x hcIoo hxIoo hcx
      have hA0 : 0 ≤ ∫ t in c..x, (1 - t ^ 2) * f1 t ^ 2 := by
        refine intervalIntegral.integral_nonneg hcx (fun t ht => ?_)
        have h1 : -1 < t := by linarith [ht.1]
        have h2 : t < 1 := lt_of_le_of_lt ht.2 hx1
        have h3 : (0 : ℝ) ≤ 1 - t ^ 2 := by nlinarith
        positivity
      have hB := spheroidal_integral_inv_one_sub_sq_le hc0 hcx hx1
      rw [hcτ] at hB
      have hB0 := spheroidal_integral_inv_one_sub_sq_nonneg hcIoo.1 hcx hx1
      have hsq := spheroidal_sq_sub_le f f1 hd hf1c hcIoo hxIoo hcx
      have hprod : (f x - f c) ^ 2 ≤ D * (Real.log τ - Real.log (1 - x)) :=
        le_trans hsq (mul_le_mul hA hB hB0 hD0)
      have hexp : f x ^ 2 ≤ 2 * f c ^ 2 + 2 * (f x - f c) ^ 2 := by
        nlinarith [sq_nonneg (f x - 2 * f c)]
      simp only [hgdef]
      linarith
    have hL : (∫ x in c..d, (Real.log τ - Real.log (1 - x))) = H d - H c :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => hHderiv x (by rw [uIcc_of_le hcd] at hx; exact lt_of_le_of_lt hx.2 hd1))
        hlc.intervalIntegrable
    have hval : (∫ x in c..d, g x) = (d - c) * (2 * f c ^ 2) + 2 * D * (H d - H c) := by
      rw [hgdef]
      rw [intervalIntegral.integral_add intervalIntegrable_const
        (hlc.intervalIntegrable.const_mul (2 * D)), intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul, hL]
      simp [smul_eq_mul]
    have hHc : H c = -τ := by
      simp only [hHdef, hcτ]
      ring
    have hHd : H d ≤ 0 := by
      have h1 : (0 : ℝ) < 1 - d := by linarith
      have h2 : (1 : ℝ) - d ≤ τ := by linarith [hcd, hcτ]
      have h3 : Real.log (1 - d) ≤ Real.log τ := Real.log_le_log h1 h2
      have h4 : Real.log (1 - d) - Real.log τ - 1 ≤ 0 := by linarith
      simp only [hHdef]
      exact mul_nonpos_of_nonneg_of_nonpos h1.le h4
    have hdc : d - c ≤ τ := by linarith [hcτ]
    have hfin : (∫ x in c..d, g x) ≤ 2 * τ * f c ^ 2 + 2 * D * τ := by
      rw [hval, hHc]
      nlinarith [sq_nonneg (f c), hD0, hHd]
    linarith
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  set d := max c (1 - ε / (M + 1)) with hddef
  have hcd : c ≤ d := le_max_left _ _
  have hd1 : d < 1 := by
    refine max_lt hc1 ?_
    have : 0 < ε / (M + 1) := by positivity
    linarith
  have hsplit : (∫ x in c..(1 : ℝ), f x ^ 2)
      = (∫ x in c..d, f x ^ 2) + (∫ x in d..(1 : ℝ), f x ^ 2) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hisq c d ⟨by linarith, hc1.le⟩ ⟨by linarith, hd1.le⟩)
      (hisq d 1 ⟨by linarith, hd1.le⟩ ⟨by norm_num, le_refl 1⟩)).symm
  have htail : (∫ x in d..(1 : ℝ), f x ^ 2) ≤ (1 - d) * M := by
    have h := intervalIntegral.integral_mono_on hd1.le
      (hisq d 1 ⟨by linarith, hd1.le⟩ ⟨by norm_num, le_refl 1⟩)
      (intervalIntegrable_const (c := M)) (fun x hx => hM x ⟨by linarith [hx.1], hx.2⟩)
    simpa [smul_eq_mul] using h
  have hlast : (1 - d) * M ≤ ε := by
    have h1 : 1 - d ≤ ε / (M + 1) := by
      have h := le_max_right c (1 - ε / (M + 1))
      linarith
    have h2 : (0 : ℝ) < M + 1 := by linarith
    calc (1 - d) * M ≤ (ε / (M + 1)) * M := mul_le_mul_of_nonneg_right h1 hM0
      _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ h2]
          nlinarith
  linarith [key d hcd hd1]
/-! ## Grönwall estimates: a priori bounds and dependence on the eigenvalue parameter -/

/-- A Lipschitz constant may always be enlarged. -/
theorem lipschitzOnWith_weaken {α β : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    {K K' : NNReal} {F : α → β} {s : Set α} (h : LipschitzOnWith K F s) (hKK : K ≤ K') :
    LipschitzOnWith K' F s := fun _ hx _ hy =>
  le_trans (h hx hy) (by gcongr)

/-- **A priori bound.** On `[0,c]` with `c < 1`, a solution of the spheroidal system grows at
most exponentially, with rate the Lipschitz constant of the field. -/
theorem spheroidal_apriori_bound (G Λ c L : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hL : (2 + |G| + |Λ + G|) / (1 - c ^ 2) + 1 ≤ L)
    (f f1 f2 : ℝ → ℝ)
    (hfd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x)
    (hfe : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Λ + G) * f x)
    {x : ℝ} (hx : x ∈ Icc 0 c) :
    max |f x| |f1 x| ≤ max |f 0| |f1 0| * Real.exp (L * x) := by
  have hcsq : 0 < 1 - c ^ 2 := by nlinarith
  set L0 := (2 + |G| + |Λ + G|) / (1 - c ^ 2) + 1 with hL0def
  have hL00 : 0 ≤ L0 := by positivity
  have hLnn : 0 ≤ L := le_trans hL00 hL
  set v : ℝ → ℝ × ℝ → ℝ × ℝ :=
    fun t p => (p.2, (2 * t * p.2 + (G * t ^ 2 - (Λ + G)) * p.1) / (1 - t ^ 2)) with hv
  set F : ℝ → ℝ × ℝ := fun t => (f t, f1 t) with hF
  have hsub : Icc (0 : ℝ) c ⊆ Ioo (-1 : ℝ) 1 :=
    fun t ht => ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hc1⟩
  have hlip : ∀ t ∈ Ico (0 : ℝ) c, LipschitzOnWith ⟨L, hLnn⟩ (v t) univ := by
    intro t ht
    have h := spheroidal_field_lipschitzOnWith G Λ c hc1 hcsq L0 hL0def hL00 t
      ⟨by linarith [ht.1], ht.2⟩
    exact lipschitzOnWith_weaken h (by exact_mod_cast hL)
  have hne : ∀ t ∈ Icc (0 : ℝ) c, (1 : ℝ) - t ^ 2 ≠ 0 := by
    intro t ht
    have h := hsub ht
    nlinarith [h.1, h.2]
  have hFderiv : ∀ t ∈ Ico (0 : ℝ) c, HasDerivWithinAt F (v t (F t)) (Ici t) t := by
    intro t ht
    have htc : t ∈ Icc (0 : ℝ) c := ⟨ht.1, ht.2.le⟩
    have hd := hfd t (hsub htc)
    have hde : HasDerivAt F (f1 t, f2 t) t := hd.1.prodMk hd.2
    have heq : v t (F t) = (f1 t, f2 t) := by
      have hodd := hfe t (hsub htc)
      have hnz := hne t htc
      simp only [hv, hF, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      field_simp
      linarith
    rw [heq]
    exact hde.hasDerivWithinAt
  have hFcont : ContinuousOn F (Icc (0 : ℝ) c) := by
    intro t ht
    have hd := hfd t (hsub ht)
    exact ((hd.1.continuousAt.prodMk hd.2.continuousAt)).continuousWithinAt
  have hzeroderiv : ∀ t ∈ Ico (0 : ℝ) c,
      HasDerivWithinAt (fun _ : ℝ => ((0 : ℝ), (0 : ℝ))) (v t ((0 : ℝ), (0 : ℝ))) (Ici t) t := by
    intro t ht
    have : v t ((0 : ℝ), (0 : ℝ)) = (0, 0) := by simp [hv]
    rw [this]
    exact (hasDerivAt_const t ((0 : ℝ), (0 : ℝ))).hasDerivWithinAt
  have hinit : dist (F 0) ((0 : ℝ), (0 : ℝ)) ≤ max |f 0| |f1 0| := by
    simp [hF, Prod.dist_eq]
  have key := dist_le_of_trajectories_ODE_of_mem (v := v) (s := fun _ => univ)
    (K := ⟨L, hLnn⟩) hlip hFcont hFderiv (fun _ _ => mem_univ _) continuousOn_const
    hzeroderiv (fun _ _ => mem_univ _) hinit x hx
  have hd : dist (F x) ((0 : ℝ), (0 : ℝ)) = max |f x| |f1 x| := by
    simp [hF, Prod.dist_eq]
  rw [hd] at key
  simpa using key

/-- **Dependence on the parameter.** Two solutions with the same initial data at `0` but
eigenvalue parameters `Λ` and `Λ'` stay close on `[0,c]`, with an error proportional to
`|Λ - Λ'|`. -/
theorem spheroidal_param_dependence (G Λ Λ' c L P : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hL : (2 + |G| + |Λ + G|) / (1 - c ^ 2) + 1 ≤ L) (hL1 : 1 ≤ L) (hP0 : 0 ≤ P)
    (f f1 f2 g g1 g2 : ℝ → ℝ)
    (hfd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x)
    (hgd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt g (g1 x) x ∧ HasDerivAt g1 (g2 x) x)
    (hfe : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Λ + G) * f x)
    (hge : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * g2 x + 2 * x * g1 x + G * x ^ 2 * g x = (Λ' + G) * g x)
    (hgP : ∀ t ∈ Icc (0 : ℝ) c, |g t| ≤ P)
    (h0 : f 0 = g 0) (h1 : f1 0 = g1 0)
    {x : ℝ} (hx : x ∈ Icc 0 c) :
    |f x - g x| ≤ |Λ - Λ'| * P / (1 - c ^ 2) * Real.exp (L * c) := by
  have hcsq : 0 < 1 - c ^ 2 := by nlinarith
  set L0 := (2 + |G| + |Λ + G|) / (1 - c ^ 2) + 1 with hL0def
  have hL00 : 0 ≤ L0 := by positivity
  have hLnn : 0 ≤ L := by linarith
  set ε := |Λ - Λ'| * P / (1 - c ^ 2) with hεdef
  have hε0 : 0 ≤ ε := by positivity
  set v : ℝ → ℝ × ℝ → ℝ × ℝ :=
    fun t p => (p.2, (2 * t * p.2 + (G * t ^ 2 - (Λ + G)) * p.1) / (1 - t ^ 2)) with hv
  set F : ℝ → ℝ × ℝ := fun t => (f t, f1 t) with hF
  set Gg : ℝ → ℝ × ℝ := fun t => (g t, g1 t) with hGg
  have hsub : Icc (0 : ℝ) c ⊆ Ioo (-1 : ℝ) 1 :=
    fun t ht => ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hc1⟩
  have hlip : ∀ t ∈ Ico (0 : ℝ) c, LipschitzOnWith ⟨L, hLnn⟩ (v t) univ := by
    intro t ht
    have h := spheroidal_field_lipschitzOnWith G Λ c hc1 hcsq L0 hL0def hL00 t
      ⟨by linarith [ht.1], ht.2⟩
    exact lipschitzOnWith_weaken h (by exact_mod_cast hL)
  have hne : ∀ t ∈ Icc (0 : ℝ) c, (1 : ℝ) - t ^ 2 ≠ 0 := by
    intro t ht
    have h := hsub ht
    nlinarith [h.1, h.2]
  have hFderiv : ∀ t ∈ Ico (0 : ℝ) c, HasDerivWithinAt F (f1 t, f2 t) (Ici t) t := by
    intro t ht
    have htc : t ∈ Icc (0 : ℝ) c := ⟨ht.1, ht.2.le⟩
    have hd := hfd t (hsub htc)
    exact (hd.1.prodMk hd.2).hasDerivWithinAt
  have hGderiv : ∀ t ∈ Ico (0 : ℝ) c, HasDerivWithinAt Gg (g1 t, g2 t) (Ici t) t := by
    intro t ht
    have htc : t ∈ Icc (0 : ℝ) c := ⟨ht.1, ht.2.le⟩
    have hd := hgd t (hsub htc)
    exact (hd.1.prodMk hd.2).hasDerivWithinAt
  have hFcont : ContinuousOn F (Icc (0 : ℝ) c) := by
    intro t ht
    have hd := hfd t (hsub ht)
    exact ((hd.1.continuousAt.prodMk hd.2.continuousAt)).continuousWithinAt
  have hGcont : ContinuousOn Gg (Icc (0 : ℝ) c) := by
    intro t ht
    have hd := hgd t (hsub ht)
    exact ((hd.1.continuousAt.prodMk hd.2.continuousAt)).continuousWithinAt
  have hFbound : ∀ t ∈ Ico (0 : ℝ) c, dist ((f1 t, f2 t) : ℝ × ℝ) (v t (F t)) ≤ 0 := by
    intro t ht
    have htc : t ∈ Icc (0 : ℝ) c := ⟨ht.1, ht.2.le⟩
    have heq : v t (F t) = (f1 t, f2 t) := by
      have hodd := hfe t (hsub htc)
      have hnz := hne t htc
      simp only [hv, hF, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      field_simp
      linarith
    rw [heq]
    simp
  have hGbound : ∀ t ∈ Ico (0 : ℝ) c, dist ((g1 t, g2 t) : ℝ × ℝ) (v t (Gg t)) ≤ ε := by
    intro t ht
    have htc : t ∈ Icc (0 : ℝ) c := ⟨ht.1, ht.2.le⟩
    have hnz := hne t htc
    have htsq : 1 - c ^ 2 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have htpos : (0 : ℝ) < 1 - t ^ 2 := by linarith
    have hodd := hge t (hsub htc)
    have hsecond : (2 * t * g1 t + (G * t ^ 2 - (Λ + G)) * g t) / (1 - t ^ 2) - g2 t
        = (Λ' - Λ) * g t / (1 - t ^ 2) := by
      field_simp
      linarith
    rw [Prod.dist_eq]
    simp only [hv, hGg]
    refine max_le (by simpa using hε0) ?_
    rw [Real.dist_eq]
    have : |g2 t - (2 * t * g1 t + (G * t ^ 2 - (Λ + G)) * g t) / (1 - t ^ 2)|
        = |Λ' - Λ| * |g t| / (1 - t ^ 2) := by
      rw [show g2 t - (2 * t * g1 t + (G * t ^ 2 - (Λ + G)) * g t) / (1 - t ^ 2)
          = -((Λ' - Λ) * g t / (1 - t ^ 2)) by linarith [hsecond]]
      rw [abs_neg, abs_div, abs_mul, abs_of_pos htpos]
    rw [this, hεdef]
    have habs : |Λ' - Λ| = |Λ - Λ'| := abs_sub_comm _ _
    rw [habs]
    have h1 : |Λ - Λ'| * |g t| ≤ |Λ - Λ'| * P :=
      mul_le_mul_of_nonneg_left (hgP t htc) (abs_nonneg _)
    have h2 : (0 : ℝ) ≤ |Λ - Λ'| * P := by positivity
    rw [← sub_nonneg]
    have hrw : |Λ - Λ'| * P / (1 - c ^ 2) - |Λ - Λ'| * |g t| / (1 - t ^ 2)
        = (|Λ - Λ'| * P * (1 - t ^ 2) - |Λ - Λ'| * |g t| * (1 - c ^ 2))
          / ((1 - c ^ 2) * (1 - t ^ 2)) := by
      field_simp
    rw [hrw]
    apply div_nonneg
    · nlinarith [h1, abs_nonneg (Λ - Λ'), abs_nonneg (g t)]
    · positivity
  have hinit : dist (F 0) (Gg 0) ≤ 0 := by
    simp [hF, hGg, h0, h1]
  have key := dist_le_of_approx_trajectories_ODE_of_mem (v := v) (s := fun _ => univ)
    (K := ⟨L, hLnn⟩) hlip hFcont hFderiv hFbound (fun _ _ => mem_univ _) hGcont hGderiv
    hGbound (fun _ _ => mem_univ _) hinit x hx
  have hKne : (L : ℝ) ≠ 0 := by linarith
  have hgb : gronwallBound 0 L (0 + ε) (x - 0) ≤ ε * Real.exp (L * c) := by
    rw [gronwallBound_of_K_ne_0 hKne]
    simp only [zero_mul, zero_add, sub_zero]
    have h1 : Real.exp (L * x) ≤ Real.exp (L * c) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hx.1, hx.2]
    have h2 : (0 : ℝ) < Real.exp (L * x) := Real.exp_pos _
    have h3 : ε / L ≤ ε := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have h4 : (1 : ℝ) ≤ Real.exp (L * x) := by
      have h5 := Real.exp_le_exp.mpr (mul_nonneg hLnn hx.1)
      simpa using h5
    calc ε / L * (Real.exp (L * x) - 1) ≤ ε * (Real.exp (L * x) - 1) :=
          mul_le_mul_of_nonneg_right h3 (by linarith)
      _ ≤ ε * Real.exp (L * c) := by
          refine mul_le_mul_of_nonneg_left ?_ hε0
          linarith
  have hfin : |f x - g x| ≤ ε * Real.exp (L * c) := by
    have hle : |f x - g x| ≤ dist (F x) (Gg x) := by
      rw [Prod.dist_eq]
      exact le_trans (le_of_eq (Real.dist_eq (f x) (g x)).symm) (le_max_left _ _)
    have key' : dist (F x) (Gg x) ≤ gronwallBound 0 L (0 + ε) (x - 0) := key
    linarith [le_trans hle key', hgb]
  exact hfin
/-! ## A uniform endpoint tail bound for eigenfunctions -/

/-- Reflection formula for the integral of the square of an even function. -/
theorem integral_sq_even_reflect (f : ℝ → ℝ) (hev : ∀ x : ℝ, f (-x) = f x) (a b : ℝ) :
    (∫ x in a..b, f x ^ 2) = ∫ x in (-b)..(-a), f x ^ 2 := by
  rw [← intervalIntegral.integral_comp_neg (fun x => f x ^ 2)]
  simp [hev]

/-- For an even function, the mass on `[-1,1]` is twice the mass on `[0,1]`. -/
theorem integral_sq_even_half (f : ℝ → ℝ) (hev : ∀ x : ℝ, f (-x) = f x)
    (hcf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    (∫ x in (-1 : ℝ)..1, f x ^ 2) = 2 * ∫ x in (0 : ℝ)..1, f x ^ 2 := by
  have hisq : ∀ u v : ℝ, u ∈ Icc (-1 : ℝ) 1 → v ∈ Icc (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => f x ^ 2) volume u v := by
    intro u v hu hv
    exact ContinuousOn.intervalIntegrable
      ((hcf.mono ((Set.ordConnected_Icc).uIcc_subset hu hv)).pow 2)
  have hsplit : (∫ x in (-1 : ℝ)..0, f x ^ 2) + (∫ x in (0 : ℝ)..1, f x ^ 2)
      = ∫ x in (-1 : ℝ)..1, f x ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals
      (hisq (-1) 0 (by norm_num) (by norm_num)) (hisq 0 1 (by norm_num) (by norm_num))
  have hrefl : (∫ x in (0 : ℝ)..1, f x ^ 2) = ∫ x in (-1 : ℝ)..(0 : ℝ), f x ^ 2 := by
    have h := integral_sq_even_reflect f hev 0 1
    simpa using h
  linarith

/-- A pointwise value of `f` is controlled by the mass of `f²` near the origin together with the
Dirichlet energy. -/
theorem spheroidal_val_sq_le (f : ℝ → ℝ) (D W : ℝ)
    (hcf : ContinuousOn f (Icc (-1 : ℝ) 1)) (x : ℝ)
    (hbd : ∀ y ∈ Icc (0 : ℝ) (1 / 2), (f x - f y) ^ 2 ≤ D * W) :
    f x ^ 2 ≤ 4 * (∫ y in (0 : ℝ)..(1 / 2), f y ^ 2) + 2 * D * W := by
  have hisq : IntervalIntegrable (fun y => f y ^ 2) volume 0 (1 / 2) := by
    refine ContinuousOn.intervalIntegrable ((hcf.mono ?_).pow 2)
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmono : (∫ _y in (0 : ℝ)..(1 / 2), f x ^ 2)
      ≤ ∫ y in (0 : ℝ)..(1 / 2), (2 * f y ^ 2 + 2 * (D * W)) := by
    refine intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const
      ((hisq.const_mul 2).add intervalIntegrable_const) (fun y hy => ?_)
    have h1 := hbd y hy
    nlinarith [sq_nonneg (f x - 2 * f y)]
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add (hisq.const_mul 2)
    intervalIntegrable_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  linarith

/-- **Uniform tail bound for eigenfunctions.** With `K` an upper bound for `Λ + |G|`, the mass of
`f²` on the endpoint layer `[1-τ,1]` is at most `τ (4 + 4K log(1/τ) + 2K)` times the total mass.
The right-hand side tends to `0` with `τ`, uniformly over all eigenfunctions with `Λ + |G| ≤ K`. -/
theorem spheroidal_tail_uniform (G Λ K τ : ℝ) (f f1 f2 : ℝ → ℝ)
    (hK0 : 0 ≤ Λ + |G|) (hKle : Λ + |G| ≤ K)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 2)
    (hev : ∀ x : ℝ, f (-x) = f x)
    (hcf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hfd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x)
    (hode : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Λ + G) * f x)
    (hlim1 : Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[<] (1 : ℝ)) (𝓝 0))
    (hlim2 : Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[>] (-1 : ℝ)) (𝓝 0)) :
    (∫ x in (1 - τ)..1, f x ^ 2)
      ≤ τ * (4 + 4 * K * (-Real.log τ) + 2 * K) * (∫ x in (-1 : ℝ)..1, f x ^ 2) := by
  have hK0' : 0 ≤ K := le_trans hK0 hKle
  have hWτ : 0 ≤ -Real.log τ := by
    have h1 : Real.log τ ≤ Real.log (1 / 2) := Real.log_le_log hτ0 hτ1
    have h2 : Real.log (1 / 2) < 0 := by
      rw [show (1 : ℝ) / 2 = 2⁻¹ by norm_num, Real.log_inv]
      simp [Real.log_pos]
    linarith
  set S := ∫ x in (-1 : ℝ)..1, f x ^ 2 with hSdef
  have hisq : ∀ u v : ℝ, u ∈ Icc (-1 : ℝ) 1 → v ∈ Icc (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => f x ^ 2) volume u v := by
    intro u v hu hv
    exact ContinuousOn.intervalIntegrable
      ((hcf.mono ((Set.ordConnected_Icc).uIcc_subset hu hv)).pow 2)
  have hS0 : 0 ≤ S := by
    rw [hSdef]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg _)
  set D := K * S with hDdef
  have hD0 : 0 ≤ D := by positivity
  have hf1c : ContinuousOn f1 (Ioo (-1 : ℝ) 1) :=
    fun x hx => ((hfd x hx).2.continuousAt).continuousWithinAt
  have hfd1 : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x := fun x hx => (hfd x hx).1
  have hDb : ∀ u v : ℝ, u ∈ Ioo (-1 : ℝ) 1 → v ∈ Ioo (-1 : ℝ) 1 → u ≤ v →
      (∫ t in u..v, (1 - t ^ 2) * f1 t ^ 2) ≤ D := by
    intro u v hu hv huv
    have h := spheroidal_dirichlet_energy_bound G Λ f f1 f2 hK0 hcf hfd hode hlim1 hlim2 hu hv huv
    have h2 : (Λ + |G|) * S ≤ K * S := mul_le_mul_of_nonneg_right hKle hS0
    rw [hDdef]
    linarith
  -- the value of `f` at the inner edge of the layer
  have hc1 : (1 : ℝ) - τ < 1 := by linarith
  have hcIoo : (1 : ℝ) - τ ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hc1⟩
  have hval : f (1 - τ) ^ 2 ≤ 4 * (∫ y in (0 : ℝ)..(1 / 2), f y ^ 2) + 2 * D * (-Real.log τ) := by
    refine spheroidal_val_sq_le f D (-Real.log τ) hcf (1 - τ) (fun y hy => ?_)
    have hy0 : 0 ≤ y := hy.1
    have hyc : y ≤ 1 - τ := by linarith [hy.2]
    have hyIoo : y ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hA := hDb y (1 - τ) hyIoo hcIoo hyc
    have hA0 : 0 ≤ ∫ t in y..(1 - τ), (1 - t ^ 2) * f1 t ^ 2 := by
      refine intervalIntegral.integral_nonneg hyc (fun t ht => ?_)
      have h1 : -1 < t := by linarith [ht.1]
      have h2 : t < 1 := by linarith [ht.2]
      have h3 : (0 : ℝ) ≤ 1 - t ^ 2 := by nlinarith
      positivity
    have hB := spheroidal_integral_inv_one_sub_sq_le hy0 hyc hc1
    have hB0 := spheroidal_integral_inv_one_sub_sq_nonneg hyIoo.1 hyc hc1
    have hBle : Real.log (1 - y) - Real.log (1 - (1 - τ)) ≤ -Real.log τ := by
      have h1 : Real.log (1 - y) ≤ 0 := by
        refine Real.log_nonpos (by linarith) (by linarith)
      have h2 : (1 : ℝ) - (1 - τ) = τ := by ring
      rw [h2]
      linarith
    have hsq := spheroidal_sq_sub_le f f1 hfd1 hf1c hyIoo hcIoo hyc
    have hle := le_trans hsq (mul_le_mul hA (le_trans hB hBle) hB0 hD0)
    have hswap : (f (1 - τ) - f y) ^ 2 = (f y - f (1 - τ)) ^ 2 := by ring
    linarith [hle]
  -- the mass on `[0,1/2]` is at most half the total mass
  have hhalf : (∫ y in (0 : ℝ)..(1 / 2), f y ^ 2) ≤ S / 2 := by
    have h1 : (∫ y in (0 : ℝ)..(1 / 2), f y ^ 2) ≤ ∫ y in (0 : ℝ)..1, f y ^ 2 := by
      refine intervalIntegral.integral_mono_interval (le_refl 0) (by norm_num) (by norm_num)
        (Filter.Eventually.of_forall (fun x => sq_nonneg (f x)))
        (hisq 0 1 (by norm_num) (by norm_num))
    have h2 := integral_sq_even_half f hev hcf
    rw [← hSdef] at h2
    linarith
  have htail := spheroidal_tail_bound f f1 D τ hτ0 hτ1 hcf hfd1 hf1c hD0 hDb
  have hfin : 2 * τ * f (1 - τ) ^ 2 + 2 * D * τ
      ≤ τ * (4 + 4 * K * (-Real.log τ) + 2 * K) * S := by
    have h1 : f (1 - τ) ^ 2 ≤ 2 * S + 2 * D * (-Real.log τ) := by linarith
    have h2 : 2 * τ * f (1 - τ) ^ 2 ≤ 2 * τ * (2 * S + 2 * D * (-Real.log τ)) := by
      apply mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 : D = K * S := hDdef
    nlinarith [hτ0.le, hS0, hK0', hWτ]
  linarith
/-! ## Normalised eigenfunctions and elementary separation facts -/

/-- Every regular even eigenvalue has an eigenfunction normalised by `f 0 = 1`, whose derivative
vanishes at the origin. -/
theorem spheroidal_normalized_witness {G Λ : ℝ} (h : RegularEvenSpheroidalEigenvalue G Λ) :
    ∃ f f1 f2 : ℝ → ℝ, f 0 = 1 ∧ f1 0 = 0 ∧ (∀ x : ℝ, f (-x) = f x) ∧
      ContinuousOn f (Icc (-1 : ℝ) 1) ∧
      (∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x) ∧
      (∀ x ∈ Ioo (-1 : ℝ) 1,
        -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Λ + G) * f x) ∧
      Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[<] (1 : ℝ)) (𝓝 0) ∧
      Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[>] (-1 : ℝ)) (𝓝 0) := by
  obtain ⟨f, f1, f2, hne, hev, hc, hd, hode, hlim1, hlim2⟩ := h
  have hf0 : f 0 ≠ 0 := spheroidal_center_ne_zero G Λ f f1 f2 hne hc hev hd hode
  set k := (f 0)⁻¹ with hk
  have hk0 : k ≠ 0 := inv_ne_zero hf0
  refine ⟨fun x => k * f x, fun x => k * f1 x, fun x => k * f2 x, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact inv_mul_cancel₀ hf0
  · have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
    have := deriv_zero_of_even hev (hd 0 h0).1
    simp [this]
  · intro x; simp only []; rw [hev x]
  · exact continuousOn_const.mul hc
  · intro x hx
    exact ⟨((hd x hx).1.const_mul k), ((hd x hx).2.const_mul k)⟩
  · intro x hx
    have h := hode x hx
    have : -(1 - x ^ 2) * (k * f2 x) + 2 * x * (k * f1 x) + G * x ^ 2 * (k * f x)
        = k * (-(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x) := by ring
    rw [this, h]
    ring
  · have h := hlim1.const_mul k
    refine Tendsto.congr' ?_ (by simpa using h)
    filter_upwards with x
    ring
  · have h := hlim2.const_mul k
    refine Tendsto.congr' ?_ (by simpa using h)
    filter_upwards with x
    ring

/-- A set of reals contained in a bounded interval whose points are pairwise `δ`-separated is
finite. -/
theorem finite_of_separated {T : Set ℝ} {a b δ : ℝ} (hδ : 0 < δ) (hT : T ⊆ Icc a b)
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ ≤ |x - y|) : T.Finite := by
  have hinj : Set.InjOn (fun x : ℝ => ⌊x / δ⌋) T := by
    intro x hx y hy hxy
    by_contra hne
    have h1 := hsep x hx y hy hne
    have h2 : |x / δ - y / δ| < 1 := by
      have := Int.abs_sub_lt_one_of_floor_eq_floor (R := ℝ) (a := x / δ) (b := y / δ) hxy
      simpa using this
    rw [div_sub_div_same, abs_div, abs_of_pos hδ, div_lt_one hδ] at h2
    linarith
  refine Set.Finite.of_finite_image ?_ hinj
  refine Set.Finite.subset (Set.finite_Icc ⌊a / δ⌋ ⌊b / δ⌋) ?_
  rintro n ⟨x, hx, rfl⟩
  have hxab := hT hx
  exact ⟨Int.floor_le_floor (by gcongr; exact hxab.1), Int.floor_le_floor (by gcongr; exact hxab.2)⟩

/-- The uniform tail factor `τ (4 + 4K log (1/τ) + 2K)` can be made arbitrarily small. -/
theorem exists_small_tail_factor (K ε : ℝ) (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 / 2 ∧ τ * (4 + 4 * K * (-Real.log τ) + 2 * K) ≤ ε := by
  have hlog : Tendsto (fun x : ℝ => Real.log x * x ^ (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_log_mul_rpow_nhdsGT_zero (by norm_num)
  have hlog' : Tendsto (fun x : ℝ => Real.log x * x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine hlog.congr (fun x => ?_)
    rw [Real.rpow_one]
  have hid : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hmain : Tendsto (fun x : ℝ => x * (4 + 4 * K * (-Real.log x) + 2 * K))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => (4 + 2 * K) * x + (-(4 * K)) * (Real.log x * x))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := (hid.const_mul (4 + 2 * K)).add (hlog'.const_mul (-(4 * K)))
      simpa using this
    refine h1.congr (fun x => ?_)
    ring
  have hev : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x * (4 + 4 * K * (-Real.log x) + 2 * K) < ε := by
    have := hmain (Metric.ball_mem_nhds (0 : ℝ) hε)
    filter_upwards [this] with x hx
    have : |x * (4 + 4 * K * (-Real.log x) + 2 * K)| < ε := by
      simpa [Real.dist_eq] using hx
    exact lt_of_le_of_lt (le_abs_self _) this
  obtain ⟨τ, hτ⟩ := Filter.nonempty_of_mem (inter_mem (Ioc_mem_nhdsGT (by norm_num : (0:ℝ) < 1/2))
    hev)
  exact ⟨τ, hτ.1.1, hτ.1.2, le_of_lt hτ.2⟩
/-! ## Upper and lower bounds for the mass of a normalised eigenfunction -/

/-- Reflection formula for the integral of an even function. -/
theorem integral_even_reflect (h : ℝ → ℝ) (hev : ∀ x : ℝ, h (-x) = h x) (a b : ℝ) :
    (∫ x in a..b, h x) = ∫ x in (-b)..(-a), h x := by
  rw [← intervalIntegral.integral_comp_neg h]
  simp [hev]

/-- If an even eigenfunction is bounded by `P` on `[0,c]` and carries at most a quarter of its
mass on the layer `[c,1]`, its total mass is at most `4P²`. -/
theorem spheroidal_mass_upper (f : ℝ → ℝ) (c P : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hev : ∀ x : ℝ, f (-x) = f x) (hcf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hP : ∀ x ∈ Icc (0 : ℝ) c, |f x| ≤ P)
    (htail : (∫ x in c..1, f x ^ 2) ≤ (1 / 4) * ∫ x in (-1 : ℝ)..1, f x ^ 2) :
    (∫ x in (-1 : ℝ)..1, f x ^ 2) ≤ 4 * P ^ 2 := by
  have hisq : ∀ u v : ℝ, u ∈ Icc (-1 : ℝ) 1 → v ∈ Icc (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => f x ^ 2) volume u v := by
    intro u v hu hv
    exact ContinuousOn.intervalIntegrable
      ((hcf.mono ((Set.ordConnected_Icc).uIcc_subset hu hv)).pow 2)
  have hsplit : (∫ x in (0 : ℝ)..c, f x ^ 2) + (∫ x in c..1, f x ^ 2)
      = ∫ x in (0 : ℝ)..1, f x ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals
      (hisq 0 c (by norm_num) ⟨by linarith, hc1⟩) (hisq c 1 ⟨by linarith, hc1⟩ (by norm_num))
  have hmid : (∫ x in (0 : ℝ)..c, f x ^ 2) ≤ c * P ^ 2 := by
    have h := intervalIntegral.integral_mono_on hc0.le
      (hisq 0 c (by norm_num) ⟨by linarith, hc1⟩) (intervalIntegrable_const (c := P ^ 2))
      (fun x hx => by
        have h1 := hP x hx
        nlinarith [abs_nonneg (f x), sq_abs (f x)])
    simpa [smul_eq_mul, mul_comm] using h
  have hhalf := integral_sq_even_half f hev hcf
  nlinarith [sq_nonneg P, hc1, hc0]

/-- A normalised even eigenfunction whose derivative is bounded by `P` on `[0,c]` has mass at
least `(min c (1/(2P)))/2`. -/
theorem spheroidal_mass_lower (f f1 : ℝ → ℝ) (c P : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hP0 : 0 < P)
    (hev : ∀ x : ℝ, f (-x) = f x) (hcf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hf0 : f 0 = 1)
    (hd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x)
    (hf1c : ContinuousOn f1 (Ioo (-1 : ℝ) 1))
    (hP : ∀ x ∈ Icc (0 : ℝ) c, |f1 x| ≤ P) :
    (min c (1 / (2 * P))) / 2 ≤ ∫ x in (-1 : ℝ)..1, f x ^ 2 := by
  set r := min c (1 / (2 * P)) with hrdef
  have hr0 : 0 < r := lt_min hc0 (by positivity)
  have hrc : r ≤ c := min_le_left _ _
  have hrP : r * P ≤ 1 / 2 := by
    have h1 : r ≤ 1 / (2 * P) := min_le_right _ _
    calc r * P ≤ (1 / (2 * P)) * P := by nlinarith
      _ = 1 / 2 := by field_simp
  have hisq : ∀ u v : ℝ, u ∈ Icc (-1 : ℝ) 1 → v ∈ Icc (-1 : ℝ) 1 →
      IntervalIntegrable (fun x => f x ^ 2) volume u v := by
    intro u v hu hv
    exact ContinuousOn.intervalIntegrable
      ((hcf.mono ((Set.ordConnected_Icc).uIcc_subset hu hv)).pow 2)
  have hlow : ∀ x ∈ Icc (0 : ℝ) r, (1 : ℝ) / 4 ≤ f x ^ 2 := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hxr : x ≤ r := hx.2
    have hxc : x ≤ c := le_trans hxr hrc
    have hxIoo : Icc (0 : ℝ) x ⊆ Ioo (-1 : ℝ) 1 := by
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2, hxc]⟩
    have hsubu : uIcc (0 : ℝ) x ⊆ Ioo (-1 : ℝ) 1 := by
      rw [uIcc_of_le hx0]; exact hxIoo
    have hint : IntervalIntegrable f1 volume 0 x := (hf1c.mono hsubu).intervalIntegrable
    have hFTC : f x - f 0 = ∫ t in (0 : ℝ)..x, f1 t :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (hsubu ht)) hint).symm
    have habs : |f x - f 0| ≤ x * P := by
      rw [hFTC]
      have h1 : |∫ t in (0 : ℝ)..x, f1 t| ≤ ∫ t in (0 : ℝ)..x, |f1 t| :=
        intervalIntegral.abs_integral_le_integral_abs hx0
      have h2 : (∫ t in (0 : ℝ)..x, |f1 t|) ≤ ∫ _t in (0 : ℝ)..x, P := by
        refine intervalIntegral.integral_mono_on hx0 hint.abs intervalIntegrable_const
          (fun t ht => hP t ⟨ht.1, le_trans ht.2 hxc⟩)
      rw [intervalIntegral.integral_const] at h2
      simp only [smul_eq_mul, sub_zero] at h2
      linarith
    have hxP : x * P ≤ 1 / 2 := by nlinarith [hP0.le, hx0]
    rw [hf0] at habs
    have : (1 : ℝ) / 2 ≤ f x := by
      have := abs_le.mp (le_trans habs hxP)
      linarith [this.1]
    nlinarith
  have hmass : r / 4 ≤ ∫ x in (0 : ℝ)..r, f x ^ 2 := by
    have h := intervalIntegral.integral_mono_on hr0.le
      (intervalIntegrable_const (c := (1 : ℝ) / 4))
      (hisq 0 r (by norm_num) ⟨by linarith, by linarith [hrc, hc1]⟩) hlow
    rw [intervalIntegral.integral_const] at h
    simp only [smul_eq_mul, sub_zero] at h
    linarith
  have hmono : (∫ x in (0 : ℝ)..r, f x ^ 2) ≤ ∫ x in (0 : ℝ)..1, f x ^ 2 := by
    refine intervalIntegral.integral_mono_interval (le_refl 0) hr0.le
      (by linarith [hrc, hc1]) (Filter.Eventually.of_forall (fun x => sq_nonneg (f x)))
      (hisq 0 1 (by norm_num) (by norm_num))
  have hhalf := integral_sq_even_half f hev hcf
  linarith
/-! ## The uniform package attached to an eigenvalue below a fixed bound -/

/-- All the uniform information attached to a regular even eigenvalue `Λ ≤ b`: a normalised
eigenfunction together with two-sided bounds for its mass, the uniform tail bound and the
uniform a priori bound on compact subintervals. -/
theorem spheroidal_package (G b K Θ τ1 c1 L1 P Λ : ℝ)
    (hΛ : RegularEvenSpheroidalEigenvalue G Λ) (hΛb : Λ ≤ b)
    (hKb : b + |G| ≤ K)
    (hΘb : ∀ x : ℝ, -max G 0 ≤ x → x ≤ b → |x + G| ≤ Θ)
    (hτ10 : 0 < τ1) (hτ1h : τ1 ≤ 1 / 2) (hc1def : c1 = 1 - τ1)
    (hτ1s : τ1 * (4 + 4 * K * (-Real.log τ1) + 2 * K) ≤ 1 / 4)
    (hL1 : (2 + |G| + Θ) / (1 - c1 ^ 2) + 1 ≤ L1) (hPdef : P = Real.exp (L1 * c1)) :
    ∃ f f1 f2 : ℝ → ℝ,
      (∀ x : ℝ, f (-x) = f x) ∧ ContinuousOn f (Icc (-1 : ℝ) 1) ∧
      (∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x) ∧
      (∀ x ∈ Ioo (-1 : ℝ) 1,
        -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Λ + G) * f x) ∧
      Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[<] (1 : ℝ)) (𝓝 0) ∧
      Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[>] (-1 : ℝ)) (𝓝 0) ∧
      f 0 = 1 ∧ f1 0 = 0 ∧
      (min c1 (1 / (2 * P))) / 2 ≤ (∫ x in (-1 : ℝ)..1, f x ^ 2) ∧
      (∫ x in (-1 : ℝ)..1, f x ^ 2) ≤ 4 * P ^ 2 ∧
      (∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
        (∫ x in (1 - τ)..1, f x ^ 2)
          ≤ τ * (4 + 4 * K * (-Real.log τ) + 2 * K) * (∫ x in (-1 : ℝ)..1, f x ^ 2)) ∧
      (∀ c L : ℝ, 0 < c → c < 1 → (2 + |G| + Θ) / (1 - c ^ 2) + 1 ≤ L →
        ∀ x ∈ Icc (0 : ℝ) c, max |f x| |f1 x| ≤ Real.exp (L * c)) := by
  obtain ⟨f, f1, f2, hf0, hf10, hev, hcf, hfd, hode, hlim1, hlim2⟩ :=
    spheroidal_normalized_witness hΛ
  have hlow := spheroidal_eigenvalue_lower_bound hΛ
  have hGabs : max G 0 ≤ |G| := max_le (le_abs_self G) (abs_nonneg G)
  have hK0' : 0 ≤ Λ + |G| := by linarith
  have hKle : Λ + |G| ≤ K := by linarith
  have hΘΛ : |Λ + G| ≤ Θ := hΘb Λ hlow hΛb
  have hc10 : 0 < c1 := by rw [hc1def]; linarith
  have hc11 : c1 < 1 := by rw [hc1def]; linarith
  have hc1sq : 0 < 1 - c1 ^ 2 := by nlinarith
  have hL1nonneg : 0 ≤ L1 := by
    have h1 : (0 : ℝ) ≤ (2 + |G| + Θ) / (1 - c1 ^ 2) := by
      have hΘ0 : 0 ≤ Θ := le_trans (abs_nonneg _) hΘΛ
      positivity
    linarith
  have hP0 : 0 < P := by rw [hPdef]; exact Real.exp_pos _
  -- the a priori bound, for any admissible `c` and `L`
  have hapriori : ∀ c L : ℝ, 0 < c → c < 1 → (2 + |G| + Θ) / (1 - c ^ 2) + 1 ≤ L →
      ∀ x ∈ Icc (0 : ℝ) c, max |f x| |f1 x| ≤ Real.exp (L * c) := by
    intro c L hc0 hc1 hLc x hx
    have hcsq : 0 < 1 - c ^ 2 := by nlinarith
    have hLmono : (2 + |G| + |Λ + G|) / (1 - c ^ 2) + 1 ≤ L := by
      have h1 : (2 + |G| + |Λ + G|) / (1 - c ^ 2) ≤ (2 + |G| + Θ) / (1 - c ^ 2) := by
        gcongr
      linarith
    have h := spheroidal_apriori_bound G Λ c L hc0 hc1 hLmono f f1 f2 hfd hode hx
    have hLnn : 0 ≤ L := by
      have h1 : (0 : ℝ) ≤ (2 + |G| + |Λ + G|) / (1 - c ^ 2) := by positivity
      linarith
    have hinit : max |f 0| |f1 0| = 1 := by
      rw [hf0, hf10]
      simp
    rw [hinit, one_mul] at h
    refine le_trans h (Real.exp_le_exp.mpr ?_)
    nlinarith [hx.1, hx.2]
  -- the uniform tail bound
  have htailall : ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
      (∫ x in (1 - τ)..1, f x ^ 2)
        ≤ τ * (4 + 4 * K * (-Real.log τ) + 2 * K) * (∫ x in (-1 : ℝ)..1, f x ^ 2) := by
    intro τ hτ0 hτh
    exact spheroidal_tail_uniform G Λ K τ f f1 f2 hK0' hKle hτ0 hτh hev hcf hfd hode hlim1 hlim2
  have hS0 : 0 ≤ ∫ x in (-1 : ℝ)..1, f x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg _)
  have hPbound : ∀ x ∈ Icc (0 : ℝ) c1, |f x| ≤ P ∧ |f1 x| ≤ P := by
    intro x hx
    have h := hapriori c1 L1 hc10 hc11 hL1 x hx
    rw [← hPdef] at h
    exact ⟨le_trans (le_max_left _ _) h, le_trans (le_max_right _ _) h⟩
  have hupper : (∫ x in (-1 : ℝ)..1, f x ^ 2) ≤ 4 * P ^ 2 := by
    refine spheroidal_mass_upper f c1 P hc10 hc11.le hev hcf (fun x hx => (hPbound x hx).1) ?_
    have h := htailall τ1 hτ10 hτ1h
    rw [← hc1def] at h
    have h2 : τ1 * (4 + 4 * K * (-Real.log τ1) + 2 * K) * (∫ x in (-1 : ℝ)..1, f x ^ 2)
        ≤ (1 / 4) * ∫ x in (-1 : ℝ)..1, f x ^ 2 := mul_le_mul_of_nonneg_right hτ1s hS0
    linarith
  have hf1c : ContinuousOn f1 (Ioo (-1 : ℝ) 1) :=
    fun x hx => ((hfd x hx).2.continuousAt).continuousWithinAt
  have hlower : (min c1 (1 / (2 * P))) / 2 ≤ ∫ x in (-1 : ℝ)..1, f x ^ 2 :=
    spheroidal_mass_lower f f1 c1 P hc10 hc11 hP0 hev hcf hf0 (fun x hx => (hfd x hx).1) hf1c
      (fun x hx => (hPbound x hx).2)
  exact ⟨f, f1, f2, hev, hcf, hfd, hode, hlim1, hlim2, hf0, hf10, hlower, hupper, htailall,
    hapriori⟩
/-! ## Milestone 3a: the spectrum below a bound is uniformly separated, hence finite -/

/-- **Separation of the spectrum.** For every bound `b` there is `δ > 0` such that any two
distinct regular even eigenvalues below `b` differ by at least `δ`. -/
theorem spheroidal_spectrum_separated (G b : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Λ Λ' : ℝ, RegularEvenSpheroidalEigenvalue G Λ →
      RegularEvenSpheroidalEigenvalue G Λ' → Λ ≤ b → Λ' ≤ b → Λ ≠ Λ' → δ ≤ |Λ - Λ'| := by
  set K := max (b + |G|) 0 with hKdef
  have hKb : b + |G| ≤ K := le_max_left _ _
  set Θ := |(-max G 0) + G| + |b + G| with hΘdef
  have hΘb : ∀ x : ℝ, -max G 0 ≤ x → x ≤ b → |x + G| ≤ Θ := by
    intro x h1 h2
    rcases le_total 0 (x + G) with h | h
    · rw [abs_of_nonneg h]
      have e1 := le_abs_self (b + G)
      have e2 := abs_nonneg ((-max G 0) + G)
      rw [hΘdef]
      linarith
    · rw [abs_of_nonpos h]
      have e1 := neg_abs_le ((-max G 0) + G)
      have e2 := abs_nonneg (b + G)
      rw [hΘdef]
      linarith
  have hΘ0 : 0 ≤ Θ := by rw [hΘdef]; positivity
  obtain ⟨τ1, hτ10, hτ1h, hτ1s⟩ := exists_small_tail_factor K (1 / 4) (by norm_num)
  set c1 := 1 - τ1 with hc1def
  have hc10 : 0 < c1 := by rw [hc1def]; linarith
  have hc11 : c1 < 1 := by rw [hc1def]; linarith
  have hc1sq : 0 < 1 - c1 ^ 2 := by nlinarith
  set L1 := (2 + |G| + Θ) / (1 - c1 ^ 2) + 1 with hL1def
  set P := Real.exp (L1 * c1) with hPdef
  have hP0 : 0 < P := Real.exp_pos _
  set Smin := (min c1 (1 / (2 * P))) / 2 with hSmindef
  have hSmin0 : 0 < Smin := by
    have : 0 < min c1 (1 / (2 * P)) := lt_min hc10 (by positivity)
    rw [hSmindef]; linarith
  set Smax := 4 * P ^ 2 with hSmaxdef
  have hSmax0 : 0 < Smax := by rw [hSmaxdef]; positivity
  obtain ⟨τ2, hτ20, hτ2h, hτ2s⟩ := exists_small_tail_factor K (Smin / (8 * Smax)) (by positivity)
  set Ψ2 := τ2 * (4 + 4 * K * (-Real.log τ2) + 2 * K) with hΨ2def
  have hlogτ2 : 0 ≤ -Real.log τ2 := by
    have h1 : Real.log τ2 ≤ Real.log (1 / 2) := Real.log_le_log hτ20 hτ2h
    have h2 : Real.log (1 / 2) < 0 := by
      rw [show (1 : ℝ) / 2 = 2⁻¹ by norm_num, Real.log_inv]
      simp [Real.log_pos]
    linarith
  have hΨ20 : 0 ≤ Ψ2 := by rw [hΨ2def]; positivity
  set c2 := 1 - τ2 with hc2def
  have hc20 : 0 < c2 := by rw [hc2def]; linarith
  have hc21 : c2 < 1 := by rw [hc2def]; linarith
  have hc2sq : 0 < 1 - c2 ^ 2 := by nlinarith
  set L2 := (2 + |G| + Θ) / (1 - c2 ^ 2) + 1 with hL2def
  have hL21 : 1 ≤ L2 := by
    have : (0 : ℝ) ≤ (2 + |G| + Θ) / (1 - c2 ^ 2) := by positivity
    rw [hL2def]; linarith
  set P2 := Real.exp (L2 * c2) with hP2def
  have hP20 : 0 < P2 := Real.exp_pos _
  set C2 := P2 / (1 - c2 ^ 2) * Real.exp (L2 * c2) with hC2def
  have hC20 : 0 < C2 := by rw [hC2def]; positivity
  refine ⟨Smin / (4 * P2 * C2), by positivity, ?_⟩
  intro Λ Λ' hΛ hΛ' hΛb hΛ'b hne
  obtain ⟨f, f1, f2, hevf, hcf, hfd, hfe, hflim1, hflim2, hf0, hf10, hfSmin, hfSmax,
    hftail, hfap⟩ :=
    spheroidal_package G b K Θ τ1 c1 L1 P Λ hΛ hΛb hKb hΘb hτ10 hτ1h hc1def hτ1s
      (le_refl _) hPdef
  obtain ⟨g, g1, g2, hevg, hcg, hgd, hge, hglim1, hglim2, hg0, hg10, hgSmin, hgSmax,
    hgtail, hgap⟩ :=
    spheroidal_package G b K Θ τ1 c1 L1 P Λ' hΛ' hΛ'b hKb hΘb hτ10 hτ1h hc1def hτ1s
      (le_refl _) hPdef
  -- integrability
  have hint : ∀ (h : ℝ → ℝ), ContinuousOn h (Icc (-1 : ℝ) 1) → ∀ u v : ℝ, u ∈ Icc (-1 : ℝ) 1 →
      v ∈ Icc (-1 : ℝ) 1 → IntervalIntegrable h volume u v := by
    intro h hh u v hu hv
    exact ContinuousOn.intervalIntegrable (hh.mono ((Set.ordConnected_Icc).uIcc_subset hu hv))
  have hcfsq : ContinuousOn (fun x => f x ^ 2) (Icc (-1 : ℝ) 1) := hcf.pow 2
  have hcgsq : ContinuousOn (fun x => g x ^ 2) (Icc (-1 : ℝ) 1) := hcg.pow 2
  have hcfg : ContinuousOn (fun x => f x * g x) (Icc (-1 : ℝ) 1) := hcf.mul hcg
  have hcfd : ContinuousOn (fun x => f x * (g x - f x)) (Icc (-1 : ℝ) 1) := hcf.mul (hcg.sub hcf)
  have hm1 : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hp1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hc2m : (-c2 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hc2p : (c2 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  -- tails
  have hftail2 : (∫ x in c2..1, f x ^ 2) ≤ Ψ2 * Smax := by
    have h := hftail τ2 hτ20 hτ2h
    rw [← hc2def, ← hΨ2def] at h
    exact le_trans h (mul_le_mul_of_nonneg_left hfSmax hΨ20)
  have hgtail2 : (∫ x in c2..1, g x ^ 2) ≤ Ψ2 * Smax := by
    have h := hgtail τ2 hτ20 hτ2h
    rw [← hc2def, ← hΨ2def] at h
    exact le_trans h (mul_le_mul_of_nonneg_left hgSmax hΨ20)
  have hftailL : (∫ x in (-1 : ℝ)..(-c2), f x ^ 2) = ∫ x in c2..1, f x ^ 2 :=
    (integral_even_reflect (fun x => f x ^ 2) (fun x => by simp only [hevf]) c2 1).symm
  have hgtailL : (∫ x in (-1 : ℝ)..(-c2), g x ^ 2) = ∫ x in c2..1, g x ^ 2 :=
    (integral_even_reflect (fun x => g x ^ 2) (fun x => by simp only [hevg]) c2 1).symm
  -- orthogonality
  have horth : (∫ x in (-1 : ℝ)..1, f x * g x) = 0 :=
    spheroidal_orthogonality G Λ Λ' f f1 f2 g g1 g2 hne hcf hcg hfd hgd hfe hge hflim1 hflim2
      hglim1 hglim2
  -- pointwise bounds on the central interval
  have hrefl : ∀ x : ℝ, |x| ≤ c2 → f x = f |x| ∧ g x = g |x| := by
    intro x hx
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]; exact ⟨rfl, rfl⟩
    · rw [abs_of_nonpos h]; exact ⟨(hevf x).symm, (hevg x).symm⟩
  have hgP2 : ∀ t ∈ Icc (0 : ℝ) c2, |g t| ≤ P2 := by
    intro t ht
    have h := hgap c2 L2 hc20 hc21 (le_refl _) t ht
    rw [← hP2def] at h
    exact le_trans (le_max_left _ _) h
  have hfP2 : ∀ t ∈ Icc (0 : ℝ) c2, |f t| ≤ P2 := by
    intro t ht
    have h := hfap c2 L2 hc20 hc21 (le_refl _) t ht
    rw [← hP2def] at h
    exact le_trans (le_max_left _ _) h
  have hdiff : ∀ x : ℝ, |x| ≤ c2 → |f x - g x| ≤ C2 * |Λ - Λ'| := by
    intro x hx
    have habs : |x| ∈ Icc (0 : ℝ) c2 := ⟨abs_nonneg _, hx⟩
    have hLmono : (2 + |G| + |Λ + G|) / (1 - c2 ^ 2) + 1 ≤ L2 := by
      have h1 : (2 + |G| + |Λ + G|) / (1 - c2 ^ 2) ≤ (2 + |G| + Θ) / (1 - c2 ^ 2) := by
        gcongr
        exact hΘb Λ (spheroidal_eigenvalue_lower_bound hΛ) hΛb
      rw [hL2def]; linarith
    have h := spheroidal_param_dependence G Λ Λ' c2 L2 P2 hc20 hc21 hLmono hL21 hP20.le
      f f1 f2 g g1 g2 hfd hgd hfe hge hgP2 (by rw [hf0, hg0]) (by rw [hf10, hg10]) habs
    obtain ⟨e1, e2⟩ := hrefl x hx
    have hEq : |Λ - Λ'| * P2 / (1 - c2 ^ 2) * Real.exp (L2 * c2) = C2 * |Λ - Λ'| := by
      rw [hC2def]; ring
    rw [e1, e2, ← hEq]
    exact h
  -- split the orthogonality relation
  have hsplit : (∫ x in (-1 : ℝ)..(-c2), f x * g x) + (∫ x in (-c2)..c2, f x * g x)
      + (∫ x in c2..1, f x * g x) = 0 := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hint _ hcfg (-1) (-c2) hm1 hc2m) (hint _ hcfg (-c2) c2 hc2m hc2p),
      intervalIntegral.integral_add_adjacent_intervals
      (hint _ hcfg (-1) c2 hm1 hc2p) (hint _ hcfg c2 1 hc2p hp1)]
    exact horth
  -- the outer pieces are small
  have houter : ∀ u v : ℝ, u ∈ Icc (-1 : ℝ) 1 → v ∈ Icc (-1 : ℝ) 1 → u ≤ v →
      |∫ x in u..v, f x * g x| ≤ ((∫ x in u..v, f x ^ 2) + (∫ x in u..v, g x ^ 2)) / 2 := by
    intro u v hu hv huv
    have h1 : |∫ x in u..v, f x * g x| ≤ ∫ x in u..v, |f x * g x| :=
      intervalIntegral.abs_integral_le_integral_abs huv
    have h2 : (∫ x in u..v, |f x * g x|) ≤ ∫ x in u..v, (f x ^ 2 + g x ^ 2) / 2 := by
      refine intervalIntegral.integral_mono_on huv ((hint _ hcfg u v hu hv).abs) ?_
        (fun x _ => ?_)
      · exact (((hint _ hcfsq u v hu hv).add (hint _ hcgsq u v hu hv)).div_const 2)
      · rw [abs_mul]
        nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x), abs_nonneg (f x),
          abs_nonneg (g x)]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hint _ hcfsq u v hu hv)
      (hint _ hcgsq u v hu hv)] at h2
    linarith
  have houterR : |∫ x in c2..1, f x * g x| ≤ Ψ2 * Smax := by
    have h := houter c2 1 hc2p hp1 (by linarith)
    linarith
  have houterL : |∫ x in (-1 : ℝ)..(-c2), f x * g x| ≤ Ψ2 * Smax := by
    have h := houter (-1) (-c2) hm1 hc2m (by linarith)
    rw [hftailL, hgtailL] at h
    linarith
  -- the central piece is large
  have hcentral : (∫ x in (-c2)..c2, f x * g x)
      = (∫ x in (-c2)..c2, f x ^ 2) + ∫ x in (-c2)..c2, f x * (g x - f x) := by
    rw [← intervalIntegral.integral_add (hint _ hcfsq (-c2) c2 hc2m hc2p)
      (hint _ hcfd (-c2) c2 hc2m hc2p)]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    ring
  have hfmass : (∫ x in (-c2)..c2, f x ^ 2)
      = (∫ x in (-1 : ℝ)..1, f x ^ 2) - (∫ x in (-1 : ℝ)..(-c2), f x ^ 2)
        - ∫ x in c2..1, f x ^ 2 := by
    have h1 : (∫ x in (-1 : ℝ)..(-c2), f x ^ 2) + (∫ x in (-c2)..c2, f x ^ 2)
        + (∫ x in c2..1, f x ^ 2) = ∫ x in (-1 : ℝ)..1, f x ^ 2 := by
      rw [intervalIntegral.integral_add_adjacent_intervals
        (hint _ hcfsq (-1) (-c2) hm1 hc2m) (hint _ hcfsq (-c2) c2 hc2m hc2p),
        intervalIntegral.integral_add_adjacent_intervals
        (hint _ hcfsq (-1) c2 hm1 hc2p) (hint _ hcfsq c2 1 hc2p hp1)]
    linarith
  have hdiffint : |∫ x in (-c2)..c2, f x * (g x - f x)| ≤ 2 * P2 * (C2 * |Λ - Λ'|) := by
    have hbd : ∀ x ∈ uIoc (-c2) c2, ‖f x * (g x - f x)‖ ≤ P2 * (C2 * |Λ - Λ'|) := by
      intro x hx
      rw [uIoc_of_le (by linarith)] at hx
      have hxabs : |x| ≤ c2 := abs_le.mpr ⟨le_of_lt hx.1, hx.2⟩
      obtain ⟨e1, e2⟩ := hrefl x hxabs
      have h1 : |f x| ≤ P2 := by
        rw [e1]; exact hfP2 |x| ⟨abs_nonneg _, hxabs⟩
      have h2 : |g x - f x| ≤ C2 * |Λ - Λ'| := by
        rw [abs_sub_comm]; exact hdiff x hxabs
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) hP20.le
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := P2 * (C2 * |Λ - Λ'|)) hbd
    rw [Real.norm_eq_abs] at h
    have habs2 : |c2 - -c2| = 2 * c2 := by
      rw [show c2 - -c2 = 2 * c2 by ring, abs_of_nonneg (by linarith)]
    rw [habs2] at h
    have h3 : 2 * c2 * (P2 * (C2 * |Λ - Λ'|)) ≤ 2 * P2 * (C2 * |Λ - Λ'|) := by
      have h4 : (0 : ℝ) ≤ P2 * (C2 * |Λ - Λ'|) := by positivity
      nlinarith [hc21.le]
    linarith
  -- combine
  have hkey : Smin - 4 * (Ψ2 * Smax) ≤ 2 * P2 * (C2 * |Λ - Λ'|) := by
    have e1 := abs_le.mp houterR
    have e2 := abs_le.mp houterL
    have e3 := abs_le.mp hdiffint
    have e4 : Smin ≤ ∫ x in (-1 : ℝ)..1, f x ^ 2 := hfSmin
    linarith [hsplit, hcentral, hfmass, hftailL, hftail2]
  have hsmall : 4 * (Ψ2 * Smax) ≤ Smin / 2 := by
    have h1 : Ψ2 ≤ Smin / (8 * Smax) := by rw [hΨ2def]; exact hτ2s
    have h2 : Ψ2 * Smax ≤ (Smin / (8 * Smax)) * Smax :=
      mul_le_mul_of_nonneg_right h1 hSmax0.le
    have h3 : (Smin / (8 * Smax)) * Smax = Smin / 8 := by field_simp
    linarith
  have hfinal : Smin / 2 ≤ 2 * P2 * (C2 * |Λ - Λ'|) := by linarith
  have hrw : |Λ - Λ'| * (4 * P2 * C2) = 2 * (2 * P2 * (C2 * |Λ - Λ'|)) := by ring
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * P2 * C2), hrw]
  linarith

/-! ## Milestone 3: discreteness and exhaustiveness of the even spectrum

The two statements below are the remaining analytic input for the main theorem: the spectrum
meets every half-line `(-∞, b]` in a finite set (discreteness), and it is infinite
(exhaustiveness).  They are stated here and used to derive the main theorem; their proofs are
not yet formalised. -/

/-- **Discreteness.** Only finitely many regular even spheroidal eigenvalues lie below any given
bound. -/
theorem spheroidal_spectrum_locallyFinite (G b : ℝ) :
    ({Λ : ℝ | RegularEvenSpheroidalEigenvalue G Λ} ∩ Iic b).Finite := by
  obtain ⟨δ, hδ, hsep⟩ := spheroidal_spectrum_separated G b
  refine finite_of_separated (a := -max G 0) (b := b) hδ ?_ ?_
  · rintro x ⟨hx, hxb⟩
    exact ⟨spheroidal_eigenvalue_lower_bound hx, hxb⟩
  · rintro x ⟨hx, hxb⟩ y ⟨hy, hyb⟩ hne
    exact hsep x y hx hy hxb hyb hne

/-- **Exhaustiveness.** There are infinitely many regular even spheroidal eigenvalues.
(Not yet proved.) -/
theorem spheroidal_spectrum_infinite (G : ℝ) :
    {Λ : ℝ | RegularEvenSpheroidalEigenvalue G Λ}.Infinite := by
  sorry

/-! ## The main theorem -/

/-- **Main theorem.** For every `G`, the set of regular even spheroidal eigenvalues is the range
of a strictly monotone sequence of reals. -/
theorem spheroidal_even_spectrum (G : ℝ) :
    ∃ μ : ℕ → ℝ, StrictMono μ ∧
      range μ = {Λ : ℝ | RegularEvenSpheroidalEigenvalue G Λ} :=
  exists_strictMono_range_eq_of_locallyFinite (spheroidal_spectrum_infinite G)
    (fun b => spheroidal_spectrum_locallyFinite G b)

