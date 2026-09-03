import Q3.Proofs.RouteB.Proposition59ExplicitProductCurvatureBridge

set_option linter.mathlibStandardSet false

/-!
# Proposition 5.9 — the alternating lattice form of the curvature

Judge verdict `f788d2fa` (`REQ-2026-09-03-LATTICEWALL`), `LEAN_READY` list, six
items in the judge's order.  Everything here is a **finite-cell identity or a
finite-cell inequality**: no cofinal statement is derived from a finite identity,
and no property of the classical `Ξ` is used or claimed.
-/

noncomputable section

open Filter Set
open scoped Topology BigOperators

namespace Q3.RouteB

/-! ## Item 1 — the alternating `η(2)` zero sum

`∑_{n ≥ 1} (1 + 2(-1)^n)/n² = 0`.  Mathlib carries `hasSum_zeta_two`
(`∑ 1/n² = π²/6`, `Mathlib/NumberTheory/ZetaValues.lean`) but **no** alternating
zeta value, so `η(2) = π²/12` is derived here from the even/odd split
`(-1)^n = 2·[Even n] − 1` and the `n ↦ 2n` reindexing of `hasSum_zeta_two`. -/

/-- `∑_{n} [Even n]/n² = π²/24`: the even part of `ζ(2)`, by reindexing along
`m ↦ 2m` (`Function.Injective.hasSum_iff`). -/
theorem hasSum_even_zeta_two :
    HasSum (fun n : ℕ => if Even n then (1 : ℝ) / (n : ℝ) ^ 2 else 0)
      (Real.pi ^ 2 / 24) := by
  have hinj : Function.Injective (fun m : ℕ => 2 * m) := by
    intro a b hab
    dsimp only at hab
    omega
  have hzero : ∀ x ∉ Set.range (fun m : ℕ => 2 * m),
      (if Even x then (1 : ℝ) / (x : ℝ) ^ 2 else 0) = 0 := by
    intro x hx
    rw [if_neg]
    intro hxe
    obtain ⟨k, hk⟩ := hxe
    exact hx ⟨k, by dsimp only; omega⟩
  rw [← Function.Injective.hasSum_iff hinj hzero]
  have hcomp : (fun n : ℕ => if Even n then (1 : ℝ) / (n : ℝ) ^ 2 else 0) ∘
      (fun m : ℕ => 2 * m) = fun m : ℕ => (1 : ℝ) / 4 * (1 / (m : ℝ) ^ 2) := by
    funext m
    have hEven : Even (2 * m) := ⟨m, by ring⟩
    simp only [Function.comp_apply, if_pos hEven]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; norm_num
    · have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
      push_cast
      field_simp
      ring
  rw [hcomp]
  have hbase := hasSum_zeta_two.mul_left (1 / 4 : ℝ)
  convert hbase using 1
  ring


/-- `∑_{n ≥ 1} (-1)^n / n² = -π²/12`, i.e. `η(2) = π²/12`.  Derived, not
imported: Mathlib v4.26 has no alternating zeta value. -/
theorem hasSum_alternating_zeta_two :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n / (n : ℝ) ^ 2) (-(Real.pi ^ 2 / 12)) := by
  have hcomb := (hasSum_even_zeta_two.mul_left 2).sub hasSum_zeta_two
  have hfun : (fun n : ℕ =>
      2 * (if Even n then (1 : ℝ) / (n : ℝ) ^ 2 else 0) - (1 : ℝ) / (n : ℝ) ^ 2) =
      fun n : ℕ => (-1 : ℝ) ^ n / (n : ℝ) ^ 2 := by
    funext n
    rcases Nat.even_or_odd n with hn | hn
    · rw [if_pos hn, hn.neg_one_pow]
      ring
    · rw [if_neg (Nat.not_even_iff_odd.mpr hn), hn.neg_one_pow]
      ring
  rw [hfun] at hcomb
  convert hcomb using 1
  ring

/-- **Item 1** (`alternating eta-two sum`): `∑_{n ≥ 1} (1 + 2(-1)^n)/n² = 0`.
The `n = 0` summand is `3/0 = 0` in Lean, so the `HasSum` over all of `ℕ` is the
sum over `n ≥ 1`. -/
theorem hasSum_alternating_eta_two_zero :
    HasSum (fun n : ℕ => (1 + 2 * (-1 : ℝ) ^ n) / (n : ℝ) ^ 2) 0 := by
  have hcomb := hasSum_zeta_two.add (hasSum_alternating_zeta_two.mul_left 2)
  have hfun : (fun n : ℕ =>
      (1 : ℝ) / (n : ℝ) ^ 2 + 2 * ((-1 : ℝ) ^ n / (n : ℝ) ^ 2)) =
      fun n : ℕ => (1 + 2 * (-1 : ℝ) ^ n) / (n : ℝ) ^ 2 := by
    funext n
    ring
  rw [hfun] at hcomb
  convert hcomb using 1
  ring

#print axioms hasSum_even_zeta_two
#print axioms hasSum_alternating_zeta_two
#print axioms hasSum_alternating_eta_two_zero

/-! ## Item 2 — the normalized Proposition-5.9 lattice sample

`F(x_n)/F(0) = (-1)^n v_n / v_0`, from `proposition59PoleKernel_at_lattice_sign`
(through the exact removable sampling `proposition59RawTransform_at_lattice`)
and `proposition59RawTransform_at_zero_eq_sqrt`.  The `√L` normalisation cancels
in the ratio; this is the only place the amplification is *not* visible. -/

/-- **Item 2** (`normalized P59 sample`), complex coefficient row. -/
theorem proposition59RawTransform_normalized_at_lattice
    {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (v : ℤ → ℂ) (h0 : 0 ∈ S) (hv0 : v 0 ≠ 0)
    {j : ℤ} (hj : j ∈ S) :
    proposition59RawTransform L S v (proposition59Pole L j) /
        proposition59RawTransform L S v 0 =
      (j.negOnePow : ℂ) * v j / v 0 := by
  have hsqrt : (Real.sqrt L : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr hL
  rw [proposition59RawTransform_at_lattice hL S v hj,
    proposition59RawTransform_at_zero_eq_sqrt hL S v h0]
  field_simp

/-- The real normalized lattice sample `f(x_n) = F(x_n)/F(0)` of a **real**
even coefficient row, at the positive mode `n`. -/
def proposition59NormalizedSample (v : ℤ → ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * v (n : ℤ) / v 0

/-- **Item 2**, real row: the normalized sample is exactly the transform ratio. -/
theorem proposition59_normalizedSample_eq_ratio
    {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (v : ℤ → ℝ) (h0 : 0 ∈ S) (hv0 : v 0 ≠ 0)
    {n : ℕ} (hn : (n : ℤ) ∈ S) :
    proposition59RawTransform L S (fun k => (v k : ℂ))
          (proposition59Pole L (n : ℤ)) /
        proposition59RawTransform L S (fun k => (v k : ℂ)) 0 =
      ((proposition59NormalizedSample v n : ℝ) : ℂ) := by
  have hv0C : ((v 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hv0
  rw [proposition59RawTransform_normalized_at_lattice hL S (fun k => (v k : ℂ))
    h0 hv0C hn, proposition59NormalizedSample]
  rw [Int.cast_negOnePow_natCast ℂ n]
  push_cast
  ring

#print axioms proposition59RawTransform_normalized_at_lattice
#print axioms proposition59_normalizedSample_eq_ratio

/-! ## Item 3 — the alternating curvature identity

`κ_F = 2 ∑_{n=1}^{N} (-1)^n (F(x_n)/F(0) - 1)/x_n²  -  (L²/(2π²)) ∑_{n>N} (-1)^n/n²`,
from `proposition59_curvature_closed_form` and items 1–2. -/

/-- The real lattice point `x_n = 2πn/L`; `proposition59Pole` is its coercion. -/
def proposition59RealPole (L : ℝ) (n : ℕ) : ℝ := 2 * (n : ℝ) * Real.pi / L

theorem proposition59RealPole_ofReal (L : ℝ) (n : ℕ) :
    ((proposition59RealPole L n : ℝ) : ℂ) = proposition59Pole L (n : ℤ) := by
  rw [proposition59Pole_ofReal, proposition59RealPole]
  push_cast
  ring_nf

/-- `∑_{n=1}^{N} (-1)^n/n²`, the alternating head. -/
def proposition59AlternatingHeadZetaTwo (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (-1 : ℝ) ^ n / (n : ℝ) ^ 2

/-- `∑_{n>N} (-1)^n/n²`, the alternating tail, as a `tsum`. -/
def proposition59AlternatingTailZetaTwo (N : ℕ) : ℝ :=
  ∑' k : ℕ, (-1 : ℝ) ^ (k + N + 1) / ((k : ℝ) + N + 1) ^ 2

theorem proposition59AlternatingTailZetaTwo_hasSum (N : ℕ) :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ (k + N + 1) / ((k : ℝ) + N + 1) ^ 2)
      (-(Real.pi ^ 2 / 12) - proposition59AlternatingHeadZetaTwo N) := by
  have hrange : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext a
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hhead : ∑ i ∈ Finset.range (N + 1), (-1 : ℝ) ^ i / (i : ℝ) ^ 2 =
      proposition59AlternatingHeadZetaTwo N := by
    rw [hrange, Finset.sum_insert (by simp), proposition59AlternatingHeadZetaTwo]
    norm_num
  have hbase := (hasSum_nat_add_iff' (f := fun n : ℕ => (-1 : ℝ) ^ n / (n : ℝ) ^ 2)
    (N + 1)).mpr hasSum_alternating_zeta_two
  rw [hhead] at hbase
  refine hbase.congr_fun fun k => ?_
  have hcast : ((k + (N + 1) : ℕ) : ℝ) = (k : ℝ) + N + 1 := by push_cast; ring
  rw [hcast, show k + N + 1 = k + (N + 1) from rfl]

theorem proposition59AlternatingTailZetaTwo_eq (N : ℕ) :
    proposition59AlternatingTailZetaTwo N =
      -(Real.pi ^ 2 / 12) - proposition59AlternatingHeadZetaTwo N :=
  (proposition59AlternatingTailZetaTwo_hasSum N).tsum_eq

/-- Pairing of a symmetric integer window with its centre removed (additive
counterpart of `prod_erase_zero_Icc_symm`). -/
private theorem sum_erase_zero_Icc_symm (N : ℕ) (g : ℤ → ℝ) :
    ∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0, g k =
      ∑ k ∈ Finset.Icc 1 N, (g (k : ℤ) + g (-(k : ℤ))) := by
  classical
  induction N with
  | zero => simp
  | succ n ih =>
      have hset : (Finset.Icc (-((n : ℤ) + 1)) ((n : ℤ) + 1)).erase 0 =
          insert ((n : ℤ) + 1)
            (insert (-((n : ℤ) + 1)) ((Finset.Icc (-(n : ℤ)) (n : ℤ)).erase 0)) := by
        ext a
        simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem1 : -((n : ℤ) + 1) ∉ (Finset.Icc (-(n : ℤ)) (n : ℤ)).erase 0 := by
        simp only [Finset.mem_erase, Finset.mem_Icc]
        omega
      have hnotmem2 : ((n : ℤ) + 1) ∉
          insert (-((n : ℤ) + 1)) ((Finset.Icc (-(n : ℤ)) (n : ℤ)).erase 0) := by
        simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_Icc]
        omega
      rw [show (-(((n : ℕ) + 1 : ℕ) : ℤ)) = -((n : ℤ) + 1) by push_cast; ring,
        show ((((n : ℕ) + 1 : ℕ) : ℤ)) = (n : ℤ) + 1 by push_cast; ring,
        hset, Finset.sum_insert hnotmem2, Finset.sum_insert hnotmem1, ih,
        Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      push_cast
      ring

/-- The real form of `proposition59_curvature_closed_form`. -/
theorem proposition59_curvature_closed_form_real
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v : ℤ → ℝ) (hv : ∀ k : ℤ, v (-k) = v k)
    (hv0 : v 0 ≠ 0)
    (hzeros : ZerosRealOn Set.univ
      (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ))
        (fun k => (v k : ℂ)))) :
    proposition59Curvature L N v =
      L ^ 2 / 2 * (1 / 12 + 1 / (2 * Real.pi ^ 2 * v 0) *
        ∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0, v k / (k : ℝ) ^ 2) := by
  have h := proposition59_curvature_closed_form hL N v hv hv0 hzeros
  apply Complex.ofReal_injective
  rw [h]
  push_cast
  ring

/-- The even-row reduction of the closed form to the positive modes. -/
theorem proposition59_curvature_closed_form_positive_modes
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v : ℤ → ℝ) (hv : ∀ k : ℤ, v (-k) = v k)
    (hv0 : v 0 ≠ 0)
    (hzeros : ZerosRealOn Set.univ
      (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ))
        (fun k => (v k : ℂ)))) :
    proposition59Curvature L N v =
      L ^ 2 / 24 + L ^ 2 / (2 * Real.pi ^ 2 * v 0) *
        ∑ n ∈ Finset.Icc 1 N, v (n : ℤ) / (n : ℝ) ^ 2 := by
  have hsym : ∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0, v k / (k : ℝ) ^ 2 =
      2 * ∑ n ∈ Finset.Icc 1 N, v (n : ℤ) / (n : ℝ) ^ 2 := by
    rw [sum_erase_zero_Icc_symm N (fun k : ℤ => v k / (k : ℝ) ^ 2),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hv (n : ℤ)]
    push_cast
    ring
  rw [proposition59_curvature_closed_form_real hL N v hv hv0 hzeros, hsym]
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **Item 3** (`alternating curvature identity`). -/
theorem proposition59_alternating_curvature_identity
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v : ℤ → ℝ) (hv : ∀ k : ℤ, v (-k) = v k)
    (hv0 : v 0 ≠ 0)
    (hzeros : ZerosRealOn Set.univ
      (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ))
        (fun k => (v k : ℂ)))) :
    proposition59Curvature L N v =
      2 * ∑ n ∈ Finset.Icc 1 N,
          (-1 : ℝ) ^ n * (proposition59NormalizedSample v n - 1) /
            proposition59RealPole L n ^ 2
        - L ^ 2 / (2 * Real.pi ^ 2) * proposition59AlternatingTailZetaTwo N := by
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hL0 : (L : ℝ) ≠ 0 := hL.ne'
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      (-1 : ℝ) ^ n * (proposition59NormalizedSample v n - 1) /
          proposition59RealPole L n ^ 2 =
        L ^ 2 / (4 * Real.pi ^ 2 * v 0) * (v (n : ℤ) / (n : ℝ) ^ 2) -
          L ^ 2 / (4 * Real.pi ^ 2) * ((-1 : ℝ) ^ n / (n : ℝ) ^ 2) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have he : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    have hexp : (-1 : ℝ) ^ n * ((-1 : ℝ) ^ n * v (n : ℤ) / v 0 - 1) =
        v (n : ℤ) / v 0 - (-1 : ℝ) ^ n := by
      field_simp
      linear_combination (v (n : ℤ)) * he
    rw [proposition59NormalizedSample, proposition59RealPole, hexp]
    field_simp
    ring
  have hsum := Finset.sum_congr rfl hterm
  rw [proposition59_curvature_closed_form_positive_modes hL N v hv hv0 hzeros,
    hsum, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    proposition59AlternatingTailZetaTwo_eq, proposition59AlternatingHeadZetaTwo]
  field_simp
  ring

#print axioms proposition59AlternatingTailZetaTwo_hasSum
#print axioms proposition59_curvature_closed_form_real
#print axioms proposition59_alternating_curvature_identity

/-! ## Item 4 — the alternating tail bound

`|∑_{n>N} (-1)^n/n²| ≤ 1/(N+1)²` by the alternating-series remainder
(`alternating_series_error_bound`), hence `|T| ≤ L²/(2π²(N+1)²)`. -/

private theorem proposition59_tail_weights_antitone (N : ℕ) :
    Antitone (fun k : ℕ => 1 / ((k : ℝ) + N + 1) ^ 2) := by
  intro a b hab
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hpos : (0 : ℝ) < ((a : ℝ) + N + 1) ^ 2 := by positivity
  refine one_div_le_one_div_of_le hpos ?_
  have h1 : (0 : ℝ) ≤ (a : ℝ) + N + 1 := by positivity
  gcongr

/-- **Item 4** (`alternating tail bound`), unscaled. -/
theorem proposition59_alternating_tail_abs_le (N : ℕ) :
    |proposition59AlternatingTailZetaTwo N| ≤ 1 / ((N : ℝ) + 1) ^ 2 := by
  have hgs : Summable (fun k : ℕ => 1 / ((k : ℝ) + N + 1) ^ 2) :=
    (proposition59TailZetaTwo_hasSum N).summable
  have herr := alternating_series_error_bound (fun k : ℕ => 1 / ((k : ℝ) + N + 1) ^ 2)
    (proposition59_tail_weights_antitone N) hgs 0
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero] at herr
  have hfac : proposition59AlternatingTailZetaTwo N =
      (-1 : ℝ) ^ (N + 1) *
        ∑' i : ℕ, (-1 : ℝ) ^ i * (1 / ((i : ℝ) + N + 1) ^ 2) := by
    rw [proposition59AlternatingTailZetaTwo, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [show k + N + 1 = k + (N + 1) from rfl, pow_add]
    ring
  rw [hfac, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  refine herr.trans ?_
  norm_num

/-- The scaled alternating tail `T = (L²/(2π²)) ∑_{n>N} (-1)^n/n²` of item 3. -/
def proposition59ScaledAlternatingTail (L : ℝ) (N : ℕ) : ℝ :=
  L ^ 2 / (2 * Real.pi ^ 2) * proposition59AlternatingTailZetaTwo N

/-- **Item 4** (`alternating tail bound`), scaled: `|T| ≤ L²/(2π²(N+1)²)`. -/
theorem proposition59_scaled_alternating_tail_abs_le (L : ℝ) (N : ℕ) :
    |proposition59ScaledAlternatingTail L N| ≤
      L ^ 2 / (2 * Real.pi ^ 2 * ((N : ℝ) + 1) ^ 2) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hc : (0 : ℝ) ≤ L ^ 2 / (2 * Real.pi ^ 2) := by positivity
  rw [proposition59ScaledAlternatingTail, abs_mul, abs_of_nonneg hc]
  have h := proposition59_alternating_tail_abs_le N
  calc L ^ 2 / (2 * Real.pi ^ 2) * |proposition59AlternatingTailZetaTwo N|
      ≤ L ^ 2 / (2 * Real.pi ^ 2) * (1 / ((N : ℝ) + 1) ^ 2) := by
        exact mul_le_mul_of_nonneg_left h hc
    _ = L ^ 2 / (2 * Real.pi ^ 2 * ((N : ℝ) + 1) ^ 2) := by
        field_simp

#print axioms proposition59_alternating_tail_abs_le
#print axioms proposition59_scaled_alternating_tail_abs_le

/-! ## Item 5 — the weighted curvature inequality

For an arbitrary comparison profile `f : ℝ → ℝ` (no property of `f` is used or
needed), with `Δ_n = F(x_n)/F(0) - f(x_n)`, `W = ∑_{n≤N} |Δ_n|/n²` and
`S_f = 2∑_{n≤N}(-1)^n (f(x_n)-1)/x_n²`:
`κ_F ≤ S_f + (L²/(2π²)) W + |T|`. -/

/-- `Δ_n = F(x_n)/F(0) - f(x_n)`, the lattice error of the row `v` against the
comparison profile `f` at the node `x_n`. -/
def proposition59LatticeError (v : ℤ → ℝ) (f : ℝ → ℝ) (L : ℝ) (n : ℕ) : ℝ :=
  proposition59NormalizedSample v n - f (proposition59RealPole L n)

/-- `W = ∑_{n≤N} |Δ_n|/n²`, the weighted lattice error. -/
def proposition59WeightedLatticeError (v : ℤ → ℝ) (f : ℝ → ℝ) (L : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, |proposition59LatticeError v f L n| / (n : ℝ) ^ 2

/-- `S_f = 2∑_{n≤N}(-1)^n (f(x_n)-1)/x_n²`, the alternating head of the
comparison profile. -/
def proposition59TrialHead (f : ℝ → ℝ) (L : ℝ) (N : ℕ) : ℝ :=
  2 * ∑ n ∈ Finset.Icc 1 N,
    (-1 : ℝ) ^ n * (f (proposition59RealPole L n) - 1) /
      proposition59RealPole L n ^ 2

/-- The exact signed split of the alternating head against a comparison
profile: no inequality yet, the error term is still signed. -/
theorem proposition59_alternating_head_split
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v : ℤ → ℝ) (f : ℝ → ℝ) :
    2 * ∑ n ∈ Finset.Icc 1 N,
        (-1 : ℝ) ^ n * (proposition59NormalizedSample v n - 1) /
          proposition59RealPole L n ^ 2 =
      proposition59TrialHead f L N +
        L ^ 2 / (2 * Real.pi ^ 2) *
          ∑ n ∈ Finset.Icc 1 N,
            (-1 : ℝ) ^ n * proposition59LatticeError v f L n / (n : ℝ) ^ 2 := by
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hL0 : (L : ℝ) ≠ 0 := hL.ne'
  rw [proposition59TrialHead, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [proposition59LatticeError, proposition59RealPole]
  field_simp
  ring

/-- **Item 5** (`weighted curvature inequality`). -/
theorem proposition59_weighted_curvature_inequality
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v : ℤ → ℝ) (hv : ∀ k : ℤ, v (-k) = v k)
    (hv0 : v 0 ≠ 0)
    (hzeros : ZerosRealOn Set.univ
      (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ))
        (fun k => (v k : ℂ))))
    (f : ℝ → ℝ) :
    proposition59Curvature L N v ≤
      proposition59TrialHead f L N +
        L ^ 2 / (2 * Real.pi ^ 2) * proposition59WeightedLatticeError v f L N +
        |proposition59ScaledAlternatingTail L N| := by
  have hc : (0 : ℝ) ≤ L ^ 2 / (2 * Real.pi ^ 2) := by positivity
  have hsigned : ∑ n ∈ Finset.Icc 1 N,
      (-1 : ℝ) ^ n * proposition59LatticeError v f L n / (n : ℝ) ^ 2 ≤
      proposition59WeightedLatticeError v f L N := by
    refine Finset.sum_le_sum fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by
      have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
      positivity
    have habs : |(-1 : ℝ) ^ n * proposition59LatticeError v f L n| =
        |proposition59LatticeError v f L n| := by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    calc (-1 : ℝ) ^ n * proposition59LatticeError v f L n / (n : ℝ) ^ 2
        ≤ |(-1 : ℝ) ^ n * proposition59LatticeError v f L n| / (n : ℝ) ^ 2 := by
          gcongr
          exact le_abs_self _
      _ = |proposition59LatticeError v f L n| / (n : ℝ) ^ 2 := by rw [habs]
  have hidentity := proposition59_alternating_curvature_identity hL N v hv hv0 hzeros
  rw [hidentity, proposition59_alternating_head_split hL N v f,
    show L ^ 2 / (2 * Real.pi ^ 2) * proposition59AlternatingTailZetaTwo N =
      proposition59ScaledAlternatingTail L N from rfl]
  have htail : -proposition59ScaledAlternatingTail L N ≤
      |proposition59ScaledAlternatingTail L N| := neg_le_abs _
  have hmul := mul_le_mul_of_nonneg_left hsigned hc
  linarith

#print axioms proposition59_alternating_head_split
#print axioms proposition59_weighted_curvature_inequality

/-! ## Item 6 — the projective weighted-node inequality

The judge's Q3 constant is `π²/√45`.  It is reproduced here **exactly**, in the
project's own objects, for

* the symmetric node sum `∑_{0<|k|≤N} |f_v(x_k) - f_q(x_k)|/k²`,
* the anchor-aligned overlap `A = v₀/q₀` (the unique scalar with
  `(v - A q)₀ = 0`, i.e. the one for which `F_v` and `A·F_q` agree at `z = 0`),
* the projective defect `p = ∑_{|k|≤N} (v_k - A q_k)²`,
* the exact node sampling `‖F_v(0)‖ = √L·|v₀|`, which is where the `√L`
  amplification enters.

The verdict writes the denominator as `|centeredXi(0)|/|A|`; that substitution
needs the `Ξ`-identification of the ground transform, which is *not* available
(the verdict itself files it under `NEW_ANALYTIC_WORK`).  Recorded as
`P59_PROJECTIVE_NODE_INEQUALITY_NORMALIZATION_GAP`. -/

/-- The normalized lattice sample at a signed mode. -/
def proposition59NormalizedSampleZ (v : ℤ → ℝ) (k : ℤ) : ℝ :=
  ((k.negOnePow : ℤ) : ℝ) * v k / v 0

theorem proposition59NormalizedSampleZ_natCast (v : ℤ → ℝ) (n : ℕ) :
    proposition59NormalizedSampleZ v (n : ℤ) = proposition59NormalizedSample v n := by
  rw [proposition59NormalizedSampleZ, proposition59NormalizedSample]
  norm_num [Int.cast_negOnePow_natCast ℝ n]

/-- **Item 2** at signed modes: the signed sample is the transform ratio. -/
theorem proposition59_normalizedSampleZ_eq_ratio
    {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (v : ℤ → ℝ) (h0 : 0 ∈ S) (hv0 : v 0 ≠ 0)
    {k : ℤ} (hk : k ∈ S) :
    proposition59RawTransform L S (fun j => (v j : ℂ)) (proposition59Pole L k) /
        proposition59RawTransform L S (fun j => (v j : ℂ)) 0 =
      ((proposition59NormalizedSampleZ v k : ℝ) : ℂ) := by
  have hv0C : ((v 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hv0
  rw [proposition59RawTransform_normalized_at_lattice hL S (fun j => (v j : ℂ))
    h0 hv0C hk, proposition59NormalizedSampleZ]
  push_cast
  ring

/-- The anchor-aligned overlap `A = v₀/q₀`. -/
def proposition59AnchorOverlap (v q : ℤ → ℝ) : ℝ := v 0 / q 0

/-- The anchor-aligned residual row `r_k = v_k - A q_k`. -/
def proposition59ProjectiveResidual (v q : ℤ → ℝ) (k : ℤ) : ℝ :=
  v k - proposition59AnchorOverlap v q * q k

/-- The projective defect `p = ∑_{|k| ≤ N} r_k²`. -/
def proposition59ProjectiveDefect (v q : ℤ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), proposition59ProjectiveResidual v q k ^ 2

/-- The symmetric weighted node error between the two normalized rows. -/
def proposition59SymmetricNodeError (v q : ℤ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0,
    |proposition59NormalizedSampleZ v k - proposition59NormalizedSampleZ q k| /
      (k : ℝ) ^ 2

theorem proposition59ProjectiveResidual_zero (v q : ℤ → ℝ) (hq0 : q 0 ≠ 0) :
    proposition59ProjectiveResidual v q 0 = 0 := by
  rw [proposition59ProjectiveResidual, proposition59AnchorOverlap]
  field_simp
  ring

theorem proposition59ProjectiveResidual_neg (v q : ℤ → ℝ)
    (hv : ∀ k : ℤ, v (-k) = v k) (hq : ∀ k : ℤ, q (-k) = q k) (k : ℤ) :
    proposition59ProjectiveResidual v q (-k) = proposition59ProjectiveResidual v q k := by
  rw [proposition59ProjectiveResidual, proposition59ProjectiveResidual, hv, hq]

/-- The signed-sample difference is the residual row, rescaled by the anchor. -/
theorem proposition59NormalizedSampleZ_sub (v q : ℤ → ℝ)
    (hv0 : v 0 ≠ 0) (hq0 : q 0 ≠ 0) (k : ℤ) :
    proposition59NormalizedSampleZ v k - proposition59NormalizedSampleZ q k =
      ((k.negOnePow : ℤ) : ℝ) * proposition59ProjectiveResidual v q k / v 0 := by
  rw [proposition59NormalizedSampleZ, proposition59NormalizedSampleZ,
    proposition59ProjectiveResidual, proposition59AnchorOverlap]
  field_simp

private theorem abs_cast_negOnePow (k : ℤ) : |((k.negOnePow : ℤ) : ℝ)| = 1 := by
  rw [← Int.cast_abs, Int.abs_negOnePow]
  norm_num

/-- `p = 2 ∑_{n=1}^{N} r_n²`: the anchor node contributes nothing. -/
theorem proposition59ProjectiveDefect_eq_two_mul (v q : ℤ → ℝ)
    (hv : ∀ k : ℤ, v (-k) = v k) (hq : ∀ k : ℤ, q (-k) = q k) (hq0 : q 0 ≠ 0)
    (N : ℕ) :
    proposition59ProjectiveDefect v q N =
      2 * ∑ n ∈ Finset.Icc 1 N, proposition59ProjectiveResidual v q (n : ℤ) ^ 2 := by
  classical
  have hzero : proposition59ProjectiveResidual v q 0 ^ 2 = 0 := by
    rw [proposition59ProjectiveResidual_zero v q hq0]
    ring
  rw [proposition59ProjectiveDefect,
    ← Finset.sum_erase (Finset.Icc (-(N : ℤ)) (N : ℤ)) hzero,
    sum_erase_zero_Icc_symm N (fun k : ℤ => proposition59ProjectiveResidual v q k ^ 2),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [proposition59ProjectiveResidual_neg v q hv hq]
  ring

/-- The symmetric node error in terms of the residual row. -/
theorem proposition59SymmetricNodeError_eq (v q : ℤ → ℝ)
    (hv : ∀ k : ℤ, v (-k) = v k) (hq : ∀ k : ℤ, q (-k) = q k)
    (hv0 : v 0 ≠ 0) (hq0 : q 0 ≠ 0) (N : ℕ) :
    proposition59SymmetricNodeError v q N =
      2 / |v 0| *
        ∑ n ∈ Finset.Icc 1 N,
          |proposition59ProjectiveResidual v q (n : ℤ)| / (n : ℝ) ^ 2 := by
  classical
  have hterm : ∀ k : ℤ,
      |proposition59NormalizedSampleZ v k - proposition59NormalizedSampleZ q k| /
          (k : ℝ) ^ 2 =
        |proposition59ProjectiveResidual v q k| / (|v 0| * (k : ℝ) ^ 2) := by
    intro k
    rw [proposition59NormalizedSampleZ_sub v q hv0 hq0 k, abs_div, abs_mul,
      abs_cast_negOnePow, one_mul]
    ring
  rw [proposition59SymmetricNodeError]
  rw [Finset.sum_congr rfl (fun k _ => hterm k),
    sum_erase_zero_Icc_symm N
      (fun k : ℤ => |proposition59ProjectiveResidual v q k| / (|v 0| * (k : ℝ) ^ 2)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [proposition59ProjectiveResidual_neg v q hv hq]
  push_cast
  ring

#print axioms proposition59_normalizedSampleZ_eq_ratio
#print axioms proposition59ProjectiveDefect_eq_two_mul
#print axioms proposition59SymmetricNodeError_eq

private theorem head_zeta_four_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) ^ 4 ≤ Real.pi ^ 4 / 90 :=
  sum_le_hasSum _ (fun i _ => by positivity) hasSum_zeta_four

private theorem sqrt_zeta_four_const :
    Real.sqrt (Real.pi ^ 4 / 90) = Real.pi ^ 2 / Real.sqrt 90 := by
  rw [show Real.pi ^ 4 = (Real.pi ^ 2) ^ 2 by ring,
    Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity)]

/-- Cauchy–Schwarz with the `1/n²` weights, using `∑ 1/n⁴ = π⁴/90`
(`hasSum_zeta_four`). -/
private theorem weighted_cauchy_schwarz (N : ℕ) (r : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 N, |r n| / (n : ℝ) ^ 2 ≤
      Real.pi ^ 2 / Real.sqrt 90 *
        Real.sqrt (∑ n ∈ Finset.Icc 1 N, r n ^ 2) := by
  have hraw := Real.sum_mul_le_sqrt_mul_sqrt (Finset.Icc 1 N)
    (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (fun n : ℕ => |r n|)
  simp only at hraw
  have hL : ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) ^ 2 * |r n| =
      ∑ n ∈ Finset.Icc 1 N, |r n| / (n : ℝ) ^ 2 :=
    Finset.sum_congr rfl fun n _ => by ring
  have hA : ∑ n ∈ Finset.Icc 1 N, ((1 : ℝ) / (n : ℝ) ^ 2) ^ 2 =
      ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) ^ 4 :=
    Finset.sum_congr rfl fun n _ => by ring
  have hB : ∑ n ∈ Finset.Icc 1 N, |r n| ^ 2 = ∑ n ∈ Finset.Icc 1 N, r n ^ 2 :=
    Finset.sum_congr rfl fun n _ => sq_abs _
  rw [hL, hA, hB] at hraw
  refine hraw.trans ?_
  have hsq : Real.sqrt (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) ^ 4) ≤
      Real.pi ^ 2 / Real.sqrt 90 := by
    rw [← sqrt_zeta_four_const]
    exact Real.sqrt_le_sqrt (head_zeta_four_le N)
  exact mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg _)

private theorem sqrt_ninety_split : Real.sqrt 90 = Real.sqrt 45 * Real.sqrt 2 := by
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 45)]
  norm_num

private theorem projective_constant :
    2 * (Real.pi ^ 2 / Real.sqrt 90) = Real.pi ^ 2 / Real.sqrt 45 * Real.sqrt 2 := by
  have h45 : Real.sqrt 45 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [sqrt_ninety_split]
  field_simp
  linear_combination -hs2

/-- **Item 6** (`projective weighted-node inequality`), coefficient-row form. -/
theorem proposition59_projective_node_inequality_row
    (N : ℕ) (v q : ℤ → ℝ) (hv : ∀ k : ℤ, v (-k) = v k) (hq : ∀ k : ℤ, q (-k) = q k)
    (hv0 : v 0 ≠ 0) (hq0 : q 0 ≠ 0) :
    proposition59SymmetricNodeError v q N ≤
      Real.pi ^ 2 / Real.sqrt 45 *
        Real.sqrt (proposition59ProjectiveDefect v q N) / |v 0| := by
  have hv0abs : (0 : ℝ) < |v 0| := abs_pos.mpr hv0
  have hSrnn : (0 : ℝ) ≤
      ∑ n ∈ Finset.Icc 1 N, proposition59ProjectiveResidual v q (n : ℤ) ^ 2 :=
    Finset.sum_nonneg fun n _ => sq_nonneg _
  have hcs := weighted_cauchy_schwarz N
    (fun n : ℕ => proposition59ProjectiveResidual v q (n : ℤ))
  simp only at hcs
  have hmain : 2 * ∑ n ∈ Finset.Icc 1 N,
        |proposition59ProjectiveResidual v q (n : ℤ)| / (n : ℝ) ^ 2 ≤
      Real.pi ^ 2 / Real.sqrt 45 *
        (Real.sqrt 2 *
          Real.sqrt (∑ n ∈ Finset.Icc 1 N,
            proposition59ProjectiveResidual v q (n : ℤ) ^ 2)) := by
    have h := mul_le_mul_of_nonneg_left hcs (by norm_num : (0 : ℝ) ≤ 2)
    calc 2 * ∑ n ∈ Finset.Icc 1 N,
            |proposition59ProjectiveResidual v q (n : ℤ)| / (n : ℝ) ^ 2
        ≤ 2 * (Real.pi ^ 2 / Real.sqrt 90 *
            Real.sqrt (∑ n ∈ Finset.Icc 1 N,
              proposition59ProjectiveResidual v q (n : ℤ) ^ 2)) := h
      _ = (2 * (Real.pi ^ 2 / Real.sqrt 90)) *
            Real.sqrt (∑ n ∈ Finset.Icc 1 N,
              proposition59ProjectiveResidual v q (n : ℤ) ^ 2) := by ring
      _ = (Real.pi ^ 2 / Real.sqrt 45 * Real.sqrt 2) *
            Real.sqrt (∑ n ∈ Finset.Icc 1 N,
              proposition59ProjectiveResidual v q (n : ℤ) ^ 2) := by
            rw [projective_constant]
      _ = Real.pi ^ 2 / Real.sqrt 45 *
            (Real.sqrt 2 *
              Real.sqrt (∑ n ∈ Finset.Icc 1 N,
                proposition59ProjectiveResidual v q (n : ℤ) ^ 2)) := by ring
  rw [proposition59SymmetricNodeError_eq v q hv hq hv0 hq0 N,
    proposition59ProjectiveDefect_eq_two_mul v q hv hq hq0 N,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc 2 / |v 0| * ∑ n ∈ Finset.Icc 1 N,
          |proposition59ProjectiveResidual v q (n : ℤ)| / (n : ℝ) ^ 2
      = (2 * ∑ n ∈ Finset.Icc 1 N,
          |proposition59ProjectiveResidual v q (n : ℤ)| / (n : ℝ) ^ 2) *
            (1 / |v 0|) := by ring
    _ ≤ (Real.pi ^ 2 / Real.sqrt 45 *
          (Real.sqrt 2 *
            Real.sqrt (∑ n ∈ Finset.Icc 1 N,
              proposition59ProjectiveResidual v q (n : ℤ) ^ 2))) * (1 / |v 0|) :=
        mul_le_mul_of_nonneg_right hmain (by positivity)
    _ = Real.pi ^ 2 / Real.sqrt 45 *
          (Real.sqrt 2 *
            Real.sqrt (∑ n ∈ Finset.Icc 1 N,
              proposition59ProjectiveResidual v q (n : ℤ) ^ 2)) / |v 0| := by ring

/-- The exact node normalisation: `‖F_v(0)‖ = √L · |v₀|`. -/
theorem proposition59RawTransform_norm_at_zero
    {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (v : ℤ → ℝ) (h0 : 0 ∈ S) :
    ‖proposition59RawTransform L S (fun k => (v k : ℂ)) 0‖ =
      Real.sqrt L * |v 0| := by
  rw [proposition59RawTransform_at_zero_eq_sqrt hL S (fun k => (v k : ℂ)) h0,
    norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg L)]

/-- **Item 6** (`projective weighted-node inequality`), transform form with the
exact `√L` node amplification. -/
theorem proposition59_projective_node_inequality
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v q : ℤ → ℝ)
    (hv : ∀ k : ℤ, v (-k) = v k) (hq : ∀ k : ℤ, q (-k) = q k)
    (hv0 : v 0 ≠ 0) (hq0 : q 0 ≠ 0) :
    proposition59SymmetricNodeError v q N ≤
      Real.pi ^ 2 / Real.sqrt 45 *
        Real.sqrt (L * proposition59ProjectiveDefect v q N) /
        ‖proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ))
            (fun j => (v j : ℂ)) 0‖ := by
  have hrow := proposition59_projective_node_inequality_row N v q hv hq hv0 hq0
  have h0mem : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by simp
  have hsL : Real.sqrt L ≠ 0 := (Real.sqrt_pos.mpr hL).ne'
  have hva : |v 0| ≠ 0 := (abs_pos.mpr hv0).ne'
  rw [proposition59RawTransform_norm_at_zero hL (Finset.Icc (-(N : ℤ)) (N : ℤ)) v h0mem,
    Real.sqrt_mul hL.le]
  have hcancel : Real.pi ^ 2 / Real.sqrt 45 *
        (Real.sqrt L * Real.sqrt (proposition59ProjectiveDefect v q N)) /
        (Real.sqrt L * |v 0|) =
      Real.pi ^ 2 / Real.sqrt 45 *
        Real.sqrt (proposition59ProjectiveDefect v q N) / |v 0| := by
    field_simp
  rw [hcancel]
  exact hrow

#print axioms proposition59_projective_node_inequality_row
#print axioms proposition59RawTransform_norm_at_zero
#print axioms proposition59_projective_node_inequality

/-! ## Recorded gap — `P59_PROJECTIVE_NODE_INEQUALITY_NORMALIZATION_GAP`

The verdict's Q3 line reads

```
W_ground_trial <= pi^2/(sqrt(45)*abs(centeredXi(0)))*abs(A)*sqrt(L*p)
```

`proposition59_projective_node_inequality` proves

```
W_ground_trial <= pi^2/sqrt(45) * sqrt(L*p) / ‖F_v(0)‖
```

with `‖F_v(0)‖ = √L·|v₀|` exactly (`proposition59RawTransform_norm_at_zero`),
`A = v₀/q₀` the anchor-aligned overlap and `p` the anchor-aligned projective
defect on the window.  The constant `π²/√45` and the `√L` node amplification
match the verdict on the nose.

What does **not** transcribe is the denominator: the verdict writes
`|centeredXi(0)|/|A|` where the proof has `‖F_v(0)‖`.  Replacing one by the
other is exactly the identification of the ground transform with `Ξ` — the
verdict's own `NEW_ANALYTIC_WORK` items `P59_WEIGHTED_LATTICE_ERROR_SOURCE_BOUND`
and `Input A`.  No such statement exists in the Lean development and none is
assumed here; the inequality above is stated in the project's own objects only.
The verdict's `A` (a phase-aligned overlap of two rows) and the anchor scalar
`v₀/q₀` also need not coincide unless the rows are normalised at the anchor.

Nothing in this file is cofinal: every statement is an identity or an
inequality at a fixed `(L, N)`.
-/

end Q3.RouteB
