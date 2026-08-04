import Q3.Proofs.RouteB.D0ScaledJacobiForcedReceiver

/-!
# The mode-four Jacobi tail contraction core

This file proves only the elementary tail estimates for the proposed mode-four continued-fraction
selector.  It does not construct a spheroidal eigenvalue, a recessive solution, a PSWF, or a third
even root.
-/

open Set

noncomputable section

noncomputable def mode4JacobiG (mProject : ℕ) : ℝ :=
  (2 * Real.pi * (mProject : ℝ)) ^ 2

def mode4JacobiIndex (q : ℕ) : ℝ :=
  2 * q

noncomputable def mode4JacobiLower
    (G : ℝ) (q : ℕ) : ℝ :=
  let N := mode4JacobiIndex q
  G * (N - 1) * N / ((2 * N - 3) * (2 * N - 1))

noncomputable def mode4JacobiUpper
    (G : ℝ) (q : ℕ) : ℝ :=
  let N := mode4JacobiIndex q
  G * (N + 1) * (N + 2) / ((2 * N + 3) * (2 * N + 5))

noncomputable def mode4JacobiCenter
    (G Λ : ℝ) (q : ℕ) : ℝ :=
  let N := mode4JacobiIndex q
  N * (N + 1) -
    2 * G * (N * (N + 1) - 1) /
      ((2 * N - 1) * (2 * N + 3)) -
    Λ

noncomputable def mode4TailMap
    (G Λ : ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  mode4JacobiLower G q /
    (mode4JacobiCenter G Λ q -
      mode4JacobiUpper G q * x)

private theorem mode4JacobiG_pos
    (mProject : ℕ) (hm : 2 ≤ mProject) :
    0 < mode4JacobiG mProject := by
  have hmR : (0 : ℝ) < (mProject : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
  unfold mode4JacobiG
  positivity

theorem mode4JacobiLower_pos
    (G : ℝ) (q : ℕ) (hG : 0 < G) (hq : 3 ≤ q) :
    0 < mode4JacobiLower G q := by
  have hqR : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  unfold mode4JacobiLower mode4JacobiIndex
  apply div_pos
  · exact mul_pos (mul_pos hG (by linarith)) (by linarith)
  · exact mul_pos (by linarith) (by linarith)

theorem mode4JacobiLower_le_one_third_mul_G
    (G : ℝ) (q : ℕ) (hG : 0 < G) (hq : 3 ≤ q) :
    mode4JacobiLower G q ≤ (1 / 3 : ℝ) * G := by
  have hqR : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hden : 0 <
      (2 * (2 * (q : ℝ)) - 3) * (2 * (2 * (q : ℝ)) - 1) := by
    exact mul_pos (by linarith) (by linarith)
  unfold mode4JacobiLower mode4JacobiIndex
  rw [div_le_iff₀ hden]
  nlinarith [mul_pos hG (sq_pos_of_pos (by linarith : 0 < (q : ℝ)))]

theorem mode4JacobiUpper_pos
    (G : ℝ) (q : ℕ) (hG : 0 < G) :
    0 < mode4JacobiUpper G q := by
  have hqR : (0 : ℝ) ≤ (q : ℝ) := by positivity
  unfold mode4JacobiUpper mode4JacobiIndex
  positivity

theorem mode4JacobiUpper_le_one_quarter_mul_G
    (G : ℝ) (q : ℕ) (hG : 0 < G) :
    mode4JacobiUpper G q ≤ (1 / 4 : ℝ) * G := by
  have hqR : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hden : 0 <
      (2 * (2 * (q : ℝ)) + 3) * (2 * (2 * (q : ℝ)) + 5) := by
    positivity
  unfold mode4JacobiUpper mode4JacobiIndex
  rw [div_le_iff₀ hden]
  nlinarith [mul_pos hG (show (0 : ℝ) < 4 * (q : ℝ) + 7 by positivity)]

private theorem mode4JacobiMiddle_le_one_half_mul_G
    (G : ℝ) (q : ℕ) (hG : 0 < G) (hq : 3 ≤ q) :
    2 * G *
          (mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 1) /
        ((2 * mode4JacobiIndex q - 1) *
          (2 * mode4JacobiIndex q + 3)) ≤
      (1 / 2 : ℝ) * G := by
  have hqR : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hden : 0 <
      (2 * (2 * (q : ℝ)) - 1) * (2 * (2 * (q : ℝ)) + 3) := by
    exact mul_pos (by linarith) (by linarith)
  unfold mode4JacobiIndex
  rw [div_le_iff₀ hden]
  nlinarith

theorem mode4JacobiCenter_sub_upper_mul_lower_bound
    (G Λ x : ℝ) (q : ℕ)
    (hG : 0 < G) (hq : 3 ≤ q)
    (hsep :
      (31 / 24 : ℝ) * G ≤
        mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (hx : x ∈ Set.Icc 0 (1 / 2)) :
    (2 / 3 : ℝ) * G ≤
      mode4JacobiCenter G Λ q - mode4JacobiUpper G q * x := by
  have hmid := mode4JacobiMiddle_le_one_half_mul_G G q hG hq
  have hcenter :
      (19 / 24 : ℝ) * G ≤ mode4JacobiCenter G Λ q := by
    unfold mode4JacobiCenter
    linarith
  have hU := mode4JacobiUpper_le_one_quarter_mul_G G q hG
  have hU0 : 0 ≤ mode4JacobiUpper G q :=
    (mode4JacobiUpper_pos G q hG).le
  have hGquarter : 0 ≤ (1 / 4 : ℝ) * G := by positivity
  have hUx :
      mode4JacobiUpper G q * x ≤ (1 / 8 : ℝ) * G := by
    calc
      mode4JacobiUpper G q * x ≤ ((1 / 4 : ℝ) * G) * (1 / 2 : ℝ) :=
        mul_le_mul hU hx.2 hx.1 hGquarter
      _ = (1 / 8 : ℝ) * G := by ring
  linarith

theorem exists_mode4TailStart
    (mProject : ℕ) (hm : 2 ≤ mProject) :
    ∃ K0 : ℕ,
      3 ≤ K0 ∧
      ∀ q ≥ K0,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20 := by
  have hG : 0 < mode4JacobiG mProject := mode4JacobiG_pos mProject hm
  obtain ⟨K, hK⟩ :=
    exists_nat_gt ((31 / 24 : ℝ) * mode4JacobiG mProject + 20)
  refine ⟨max 3 K, le_max_left _ _, ?_⟩
  intro q hq
  have hKq : K ≤ q := le_trans (le_max_right 3 K) hq
  have hqR : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hlarge :
      (31 / 24 : ℝ) * mode4JacobiG mProject + 20 < (q : ℝ) :=
    lt_of_lt_of_le hK (by exact_mod_cast hKq)
  unfold mode4JacobiIndex
  nlinarith [hG]

theorem mode4TailMap_mapsTo_and_contracts
    (mProject q : ℕ)
    (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hq : 3 ≤ q)
    (hsep :
      (31 / 24 : ℝ) * mode4JacobiG mProject ≤
        mode4JacobiIndex q *
            (mode4JacobiIndex q + 1) -
          20)
    (hΛ : Λ ≤ 20) :
    Set.MapsTo
        (mode4TailMap (mode4JacobiG mProject) Λ q)
        (Set.Icc 0 (1 / 2))
        (Set.Icc 0 (1 / 2)) ∧
      LipschitzOnWith
        (3 / 16 : NNReal)
        (mode4TailMap (mode4JacobiG mProject) Λ q)
        (Set.Icc 0 (1 / 2)) := by
  let G := mode4JacobiG mProject
  let L := mode4JacobiLower G q
  let U := mode4JacobiUpper G q
  let C := mode4JacobiCenter G Λ q
  have hG : 0 < G := mode4JacobiG_pos mProject hm
  have hLpos : 0 < L := mode4JacobiLower_pos G q hG hq
  have hLle : L ≤ (1 / 3 : ℝ) * G :=
    mode4JacobiLower_le_one_third_mul_G G q hG hq
  have hUpos : 0 < U := mode4JacobiUpper_pos G q hG
  have hUle : U ≤ (1 / 4 : ℝ) * G :=
    mode4JacobiUpper_le_one_quarter_mul_G G q hG
  have hdenLower : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2),
      (2 / 3 : ℝ) * G ≤ C - U * x := by
    intro x hx
    exact mode4JacobiCenter_sub_upper_mul_lower_bound
      G Λ x q hG hq hsep hΛ hx
  have hdenPos : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2), 0 < C - U * x := by
    intro x hx
    have := hdenLower x hx
    nlinarith
  change
    Set.MapsTo (fun x : ℝ ↦ L / (C - U * x))
        (Set.Icc 0 (1 / 2)) (Set.Icc 0 (1 / 2)) ∧
      LipschitzOnWith (3 / 16 : NNReal)
        (fun x : ℝ ↦ L / (C - U * x)) (Set.Icc 0 (1 / 2))
  constructor
  · intro x hx
    constructor
    · exact div_nonneg hLpos.le (hdenPos x hx).le
    · rw [div_le_iff₀ (hdenPos x hx)]
      linarith [hdenLower x hx]
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hdx : 0 < C - U * x := hdenPos x hx
    have hdy : 0 < C - U * y := hdenPos y hy
    have hdenProduct :
        ((2 / 3 : ℝ) * G) * ((2 / 3 : ℝ) * G) ≤
          (C - U * x) * (C - U * y) :=
      mul_le_mul (hdenLower x hx) (hdenLower y hy)
        (by positivity) hdx.le
    have hnum : L * U ≤ ((1 / 3 : ℝ) * G) * ((1 / 4 : ℝ) * G) :=
      mul_le_mul hLle hUle hUpos.le (by positivity)
    have hratio :
        L * U / ((C - U * x) * (C - U * y)) ≤ (3 / 16 : ℝ) := by
      rw [div_le_iff₀ (mul_pos hdx hdy)]
      calc
        L * U ≤ ((1 / 3 : ℝ) * G) * ((1 / 4 : ℝ) * G) := hnum
        _ = (3 / 16 : ℝ) *
              (((2 / 3 : ℝ) * G) * ((2 / 3 : ℝ) * G)) := by ring
        _ ≤ (3 / 16 : ℝ) * ((C - U * x) * (C - U * y)) :=
          mul_le_mul_of_nonneg_left hdenProduct (by norm_num)
    have hdiff :
        L / (C - U * x) - L / (C - U * y) =
          (L * U / ((C - U * x) * (C - U * y))) * (x - y) := by
      field_simp [hdx.ne', hdy.ne']
      ring
    rw [Real.dist_eq, Real.dist_eq, hdiff, abs_mul]
    have hratioNonneg :
        0 ≤ L * U / ((C - U * x) * (C - U * y)) := by positivity
    rw [abs_of_nonneg hratioNonneg]
    exact mul_le_mul_of_nonneg_right hratio (abs_nonneg _)

#print axioms exists_mode4TailStart
#print axioms mode4TailMap_mapsTo_and_contracts
