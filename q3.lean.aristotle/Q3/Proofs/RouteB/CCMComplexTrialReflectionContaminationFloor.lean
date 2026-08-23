import Q3.Proofs.RouteB.CCMProposition59ComplexTrialComplementFloor

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

open Complex Matrix
open scoped BigOperators ComplexOrder

noncomputable section

namespace Q3.RouteB

/-!
# H2a.1 — reflection sector floors, odd mass and residual give the full
complement floor

Floor `H2A_1_REFLECTION_SECTOR_FLOORS_ODD_MASS_RESIDUAL_TO_COMPLEMENT_FLOOR`
of verdict `95d45029`.

The exact finite reflection-contamination transport: on a finite complex
Hilbert carrier, for a Hermitian `K` commuting with a Hermitian unitary
involution `J`, a unit trial `q` with odd mass `η < 1`, a real shift `a`,
sector floors `βp` (even sector, orthogonally to the even part of `q`) and
`βm` (odd sector), and a residual bound `ρ` on `(K - a)q`, the full literal
`q`-orthogonal complement carries the floor

`betaEff = min(βp, βm) * (1 - η) - ((2*√η + η)/√(1-η)) * ρ`.

Exact parity of the trial is neither assumed nor concluded: odd mass and
residual control replace it.  The residual term is load-bearing: the private
plant exhibits a three-dimensional reflection-commuting Hermitian example
with both sector floors equal to one and odd mass `121/3721 < 1/25` whose
literal `q`-perp contains a strictly negative energy direction once the
in-sector coupling grows — the statement with the residual hypothesis
deleted is false.

The conclusion is the existing consumable predicate
`complexTrialComplementFloor K q a betaEff`, so the already-green generic
spectral receiver applies downstream without adaptation.

Deliberately NOT here: any selected Ferrers source estimate, any cofinal
floor claim, simple even ground, Theorem 5.10, real zeros.

LEDGER:
  CLOSES: [REFLECTION_SECTOR_FLOORS_ODD_MASS_RESIDUAL_TO_FULL_COMPLEMENT_FLOOR]
  OPENS:  []
-/

/-! ## Dot-product / Euclidean inner bridge -/

private lemma dot_eq_inner {ι : Type*} [Fintype ι] (x y : ι → ℂ) :
    star x ⬝ᵥ y =
      inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ ι) (WithLp.toLp 2 y) := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct, mul_comm]

private lemma dot_self_re_eq_norm_sq {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    (star x ⬝ᵥ x).re =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ ^ 2 := by
  rw [dot_eq_inner]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

/-! ## The mandatory plant -/

/-- **The plant.**  Odd mass without residual control does not force a
complement floor.  A three-dimensional reflection-commuting Hermitian matrix
with unit sector floors and odd mass `121/3721 < 1/25` contains a strictly
negative energy direction inside the literal `q`-orthogonal complement: the
in-sector coupling `100` between the even trial direction and its even
complement destroys the floor while every non-residual hypothesis of the
main theorem continues to hold.  The residual/coupling input is
load-bearing. -/
private theorem oddMass_without_residual_control_does_not_force_complementFloor_plant :
    ∃ (K J : Matrix (Fin 3) (Fin 3) ℂ) (q : Fin 3 → ℂ) (a η βp βm : ℝ),
      K.IsHermitian ∧ J.IsHermitian ∧ J * J = 1 ∧ K * J = J * K ∧
      star q ⬝ᵥ q = 1 ∧
      η = (star ((2⁻¹ : ℂ) • (q - J *ᵥ q)) ⬝ᵥ
        ((2⁻¹ : ℂ) • (q - J *ᵥ q))).re ∧
      0 ≤ η ∧ η < 1 / 25 ∧ 0 < βp ∧ 0 < βm ∧
      (∀ x : Fin 3 → ℂ, J *ᵥ x = x →
        star ((2⁻¹ : ℂ) • (q + J *ᵥ q)) ⬝ᵥ x = 0 →
        βp * (star x ⬝ᵥ x).re ≤
          (star x ⬝ᵥ
            ((K - (a : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) *ᵥ x)).re) ∧
      (∀ x : Fin 3 → ℂ, J *ᵥ x = -x →
        βm * (star x ⬝ᵥ x).re ≤
          (star x ⬝ᵥ
            ((K - (a : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) *ᵥ x)).re) ∧
      ∃ v : Fin 3 → ℂ,
        star q ⬝ᵥ v = 0 ∧
        (star v ⬝ᵥ
          ((K - (a : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) *ᵥ v)).re < 0 := by
  classical
  set K₀ : Matrix (Fin 3) (Fin 3) ℂ := !![0, 100, 0; 100, 1, 0; 0, 0, 1]
    with hK₀
  set J₀ : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, 1, 0; 0, 0, -1]
    with hJ₀
  set q₀ : Fin 3 → ℂ := ![(60/61 : ℂ), 0, (11/61 : ℂ)] with hq₀
  have hshift : (K₀ - ((0:ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) = K₀ := by
    rw [show (((0:ℝ)) : ℂ) = 0 from Complex.ofReal_zero, zero_smul, sub_zero]
  have hJq : J₀ *ᵥ q₀ = ![(60/61 : ℂ), 0, -(11/61 : ℂ)] := by
    funext i
    fin_cases i <;>
      simp [hJ₀, hq₀, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hJx2 : ∀ x : Fin 3 → ℂ, (J₀ *ᵥ x) 2 = -(x 2) := by
    intro x
    simp [hJ₀, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hJx0 : ∀ x : Fin 3 → ℂ, (J₀ *ᵥ x) 0 = x 0 := by
    intro x
    simp [hJ₀, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hJx1 : ∀ x : Fin 3 → ℂ, (J₀ *ᵥ x) 1 = x 1 := by
    intro x
    simp [hJ₀, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  refine ⟨K₀, J₀, q₀, 0, 121/3721, 1, 1,
    ?_, ?_, ?_, ?_, ?_, ?_, by norm_num, by norm_num, one_pos, one_pos,
    ?_, ?_, ?_⟩
  · show K₀ᴴ = K₀
    rw [hK₀]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply]
  · show J₀ᴴ = J₀
    rw [hJ₀]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply]
  · rw [hJ₀]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]
  · rw [hK₀, hJ₀]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]
  · -- unit trial: (60/61)^2 + (11/61)^2 = 1
    have h : star q₀ ⬝ᵥ q₀ = (((1:ℝ)) : ℂ) := by
      simp [hq₀, dotProduct, Fin.sum_univ_three, map_div₀, map_ofNat]
      push_cast
      ring
    rw [h]
    norm_num
  · -- odd mass 121/3721
    have hvec : (2⁻¹ : ℂ) • (q₀ - J₀ *ᵥ q₀) = ![0, 0, (11/61 : ℂ)] := by
      rw [hJq]
      funext i
      fin_cases i <;> simp [hq₀] <;> norm_num
    rw [hvec]
    have hdot : star (![0, 0, (11/61 : ℂ)] : Fin 3 → ℂ) ⬝ᵥ
        ![0, 0, (11/61 : ℂ)] = (((121:ℝ)/3721 : ℝ) : ℂ) := by
      simp [dotProduct, Fin.sum_univ_three, map_div₀, map_ofNat]
      push_cast
      ring
    rw [hdot, Complex.ofReal_re]
  · -- even-sector floor with βp = 1
    intro x hJx horth
    have hx2 : x 2 = 0 := by
      have h := congrFun hJx 2
      rw [hJx2 x] at h
      linear_combination (-(1:ℂ)/2) * h
    have hx0 : x 0 = 0 := by
      have hplus : (2⁻¹ : ℂ) • (q₀ + J₀ *ᵥ q₀) = ![(60/61 : ℂ), 0, 0] := by
        rw [hJq]
        funext i
        fin_cases i <;> simp [hq₀] <;> norm_num
      rw [hplus] at horth
      have h : (starRingEnd ℂ) (60/61 : ℂ) * x 0 = 0 := by
        have h2 := horth
        simp [dotProduct, Fin.sum_univ_three] at h2
        simpa using h2
      have hc : (starRingEnd ℂ) (60/61 : ℂ) ≠ 0 := by
        rw [map_div₀, map_ofNat, map_ofNat]
        norm_num
      exact (mul_eq_zero.mp h).resolve_left hc
    rw [hshift]
    have hKx : K₀ *ᵥ x = ![100 * x 1, x 1, 0] := by
      funext i
      fin_cases i <;>
        simp [hK₀, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hx0, hx2]
    rw [hKx]
    have hL : star x ⬝ᵥ x = (starRingEnd ℂ) (x 1) * x 1 := by
      simp [dotProduct, Fin.sum_univ_three, hx0, hx2]
    have hR : star x ⬝ᵥ (![100 * x 1, x 1, 0] : Fin 3 → ℂ) =
        (starRingEnd ℂ) (x 1) * x 1 := by
      simp [dotProduct, Fin.sum_univ_three, hx0, hx2]
    rw [hL, hR, one_mul]
  · -- odd-sector floor with βm = 1
    intro x hJx
    have hx0 : x 0 = 0 := by
      have h := congrFun hJx 0
      rw [hJx0 x] at h
      have h2 : x 0 = -(x 0) := by simpa using h
      linear_combination ((1:ℂ)/2) * h2
    have hx1 : x 1 = 0 := by
      have h := congrFun hJx 1
      rw [hJx1 x] at h
      have h2 : x 1 = -(x 1) := by simpa using h
      linear_combination ((1:ℂ)/2) * h2
    rw [hshift]
    have hKx : K₀ *ᵥ x = ![0, 0, x 2] := by
      funext i
      fin_cases i <;>
        simp [hK₀, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hx0, hx1]
    rw [hKx]
    have hL : star x ⬝ᵥ x = (starRingEnd ℂ) (x 2) * x 2 := by
      simp [dotProduct, Fin.sum_univ_three, hx0, hx1]
    have hR : star x ⬝ᵥ (![0, 0, x 2] : Fin 3 → ℂ) =
        (starRingEnd ℂ) (x 2) * x 2 := by
      simp [dotProduct, Fin.sum_univ_three, hx0, hx1]
    rw [hL, hR, one_mul]
  · -- negative q-perp direction under coupling 100
    refine ⟨![(11/61 : ℂ), -1, -(60/61 : ℂ)], ?_, ?_⟩
    · have h : star q₀ ⬝ᵥ (![(11/61 : ℂ), -1, -(60/61 : ℂ)] : Fin 3 → ℂ) =
          ((0:ℝ) : ℂ) := by
        simp [hq₀, dotProduct, Fin.sum_univ_three, map_div₀, map_ofNat]
        push_cast
        ring
      rw [h]
      norm_num
    · rw [hshift]
      have hKv : K₀ *ᵥ (![(11/61 : ℂ), -1, -(60/61 : ℂ)] : Fin 3 → ℂ) =
          ![(-100 : ℂ), 1100/61 - 1, -(60/61 : ℂ)] := by
        funext i
        fin_cases i <;>
          simp [hK₀, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
          norm_num <;> ring
      rw [hKv]
      have hdot : star (![(11/61 : ℂ), -1, -(60/61 : ℂ)] : Fin 3 → ℂ) ⬝ᵥ
          (![(-100 : ℂ), 1100/61 - 1, -(60/61 : ℂ)] : Fin 3 → ℂ) =
          (((-126879 : ℝ)/3721 : ℝ) : ℂ) := by
        simp [dotProduct, Fin.sum_univ_three, map_div₀, map_ofNat,
          map_neg, map_one]
        push_cast
        ring
      rw [hdot, Complex.ofReal_re]
      norm_num

/-! ## The abstract finite reflection-contamination core -/

/-- Final real-arithmetic assembly, isolated from the vector context so that
the polynomial arithmetic stays small. -/
private lemma real_assembly
    (βp βm η ρ betaEff nv nw nvm d E : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hρ0 : 0 ≤ ρ)
    (hbeta : betaEff = min βp βm * (1 - η) -
      (2 * Real.sqrt η + η) / Real.sqrt (1 - η) * ρ)
    (hbeta0 : 0 < betaEff)
    (hnv : 0 ≤ nv) (hnw : 0 ≤ nw) (hnvm : 0 ≤ nvm) (hd : 0 ≤ d)
    (hdkey : d ^ 2 ≤ η * nv ^ 2)
    (hdle : d ≤ Real.sqrt η * nv)
    (hwle : nw ≤ nv)
    (hnormsum : nvm ^ 2 + nw ^ 2 = nv ^ 2 - d ^ 2)
    (hsum : E ≥ min βp βm * (nvm ^ 2 + nw ^ 2) -
      (ρ / Real.sqrt (1 - η)) * (d ^ 2 + 2 * d * nw)) :
    betaEff * nv ^ 2 ≤ E := by
  have h1η : (0:ℝ) < 1 - η := by linarith
  have hsq1η : (0:ℝ) < Real.sqrt (1 - η) := Real.sqrt_pos.mpr h1η
  have hsqη : (0:ℝ) ≤ Real.sqrt η := Real.sqrt_nonneg η
  have hρ' : (0:ℝ) ≤ ρ / Real.sqrt (1 - η) := by positivity
  have hβ0 : 0 < min βp βm := by
    by_contra hcon
    push_neg at hcon
    have hpen0 : 0 ≤ (2 * Real.sqrt η + η) / Real.sqrt (1 - η) * ρ := by
      positivity
    have hle : betaEff ≤ 0 := by
      rw [hbeta]
      nlinarith
    linarith
  have h7 : E ≥ min βp βm * (nv ^ 2 - d ^ 2) -
      (ρ / Real.sqrt (1 - η)) * (d ^ 2 + 2 * d * nw) := by
    have h8 := hsum
    rw [hnormsum] at h8
    exact h8
  have h3 : min βp βm * (nv ^ 2 - d ^ 2) ≥
      min βp βm * (1 - η) * nv ^ 2 := by
    nlinarith
  have h6 : d ^ 2 + 2 * d * nw ≤ (η + 2 * Real.sqrt η) * nv ^ 2 := by
    have h2 : 2 * d * nw ≤ 2 * (Real.sqrt η * nv) * nv := by
      nlinarith [mul_le_mul hdle hwle hnw (mul_nonneg hsqη hnv)]
    nlinarith
  have h5 : (ρ / Real.sqrt (1 - η)) * (d ^ 2 + 2 * d * nw) ≤
      (ρ / Real.sqrt (1 - η)) * (η + 2 * Real.sqrt η) * nv ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h6 hρ']
  have hEff : min βp βm * (1 - η) * nv ^ 2 -
      (ρ / Real.sqrt (1 - η)) * (η + 2 * Real.sqrt η) * nv ^ 2 =
      betaEff * nv ^ 2 := by
    rw [hbeta]
    ring
  linarith [h7, h3, h5, hEff.le, hEff.ge]

/-- The inner-space core: sector floors, odd mass and residual control give
the effective floor on the orthogonal complement of the trial vector.  All
operator inputs are pointwise functional hypotheses, so the lemma applies
verbatim to matrix actions. -/
private lemma core_contamination_bound
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (S T : V → V)
    (hSadd : ∀ x y, S (x + y) = S x + S y)
    (hSsmul : ∀ (c : ℂ) x, S (c • x) = c • S x)
    (hSsym : ∀ x y, inner ℂ (S x) y = inner ℂ x (S y))
    (hTadd : ∀ x y, T (x + y) = T x + T y)
    (hTsmul : ∀ (c : ℂ) x, T (c • x) = c • T x)
    (hTsym : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    (hTT : ∀ x, T (T x) = x)
    (hST : ∀ x, S (T x) = T (S x))
    (q : V) (hq : ‖q‖ = 1)
    (η βp βm ρ betaEff : ℝ)
    (hη : η = ‖(2⁻¹ : ℂ) • (q - T q)‖ ^ 2)
    (hη1 : η < 1)
    (heven : ∀ x, T x = x →
      inner ℂ ((2⁻¹ : ℂ) • (q + T q)) x = 0 →
      βp * ‖x‖ ^ 2 ≤ (inner ℂ x (S x)).re)
    (hodd : ∀ x, T x = -x →
      βm * ‖x‖ ^ 2 ≤ (inner ℂ x (S x)).re)
    (hρ0 : 0 ≤ ρ) (hρ : ‖S q‖ ≤ ρ)
    (hbeta : betaEff = min βp βm * (1 - η) -
      (2 * Real.sqrt η + η) / Real.sqrt (1 - η) * ρ)
    (hbeta0 : 0 < betaEff)
    (v : V) (hv : inner ℂ q v = 0) :
    betaEff * ‖v‖ ^ 2 ≤ (inner ℂ v (S v)).re := by
  classical
  have hη0 : 0 ≤ η := by
    rw [hη]
    positivity
  have h1η : (0:ℝ) < 1 - η := by linarith
  have hsq1η : (0:ℝ) < Real.sqrt (1 - η) := Real.sqrt_pos.mpr h1η
  have hpen0 : 0 ≤ (2 * Real.sqrt η + η) / Real.sqrt (1 - η) * ρ := by
    apply mul_nonneg (div_nonneg ?_ hsq1η.le) hρ0
    have := Real.sqrt_nonneg η
    linarith
  have hβ0 : 0 < min βp βm := by
    by_contra hcon
    push_neg at hcon
    have : betaEff ≤ 0 := by
      rw [hbeta]
      nlinarith
    linarith
  set P : V → V := fun x => (2⁻¹ : ℂ) • (x + T x) with hP
  set M : V → V := fun x => (2⁻¹ : ℂ) • (x - T x) with hM
  have hPM : ∀ x, P x + M x = x := by
    intro x
    rw [hP, hM]
    dsimp only
    rw [smul_add, smul_sub]
    have : ∀ a b : V, (2⁻¹ : ℂ) • a + (2⁻¹ : ℂ) • b +
        ((2⁻¹ : ℂ) • a - (2⁻¹ : ℂ) • b) = (2⁻¹ : ℂ) • a + (2⁻¹ : ℂ) • a := by
      intro a b
      abel
    rw [this, ← add_smul]
    norm_num
  have hPeven : ∀ x, T (P x) = P x := by
    intro x
    rw [hP]
    dsimp only
    rw [hTsmul, hTadd, hTT, add_comm]
  have hModd : ∀ x, T (M x) = -(M x) := by
    intro x
    rw [hM]
    dsimp only
    rw [hTsmul, ← smul_neg]
    congr 1
    have hneg : T (-(T x)) = -x := by
      have h2 := hTsmul (-1 : ℂ) (T x)
      simp only [neg_smul, one_smul] at h2
      rw [h2, hTT]
    calc T (x - T x) = T (x + -(T x)) := by rw [sub_eq_add_neg]
      _ = T x + T (-(T x)) := hTadd x (-(T x))
      _ = T x + -x := by rw [hneg]
      _ = -(x - T x) := by abel
  have hEO : ∀ x y, T x = x → T y = -y → inner ℂ x y = 0 := by
    intro x y hx hy
    have h1 : inner ℂ x y = inner ℂ (T x) y := by rw [hx]
    have h2 : inner ℂ (T x) y = inner ℂ x (T y) := hTsym x y
    have h3 : inner ℂ x (T y) = -(inner ℂ x y) := by
      rw [hy, inner_neg_right]
    have h4 : inner ℂ x y = -(inner ℂ x y) := h1.trans (h2.trans h3)
    linear_combination (2⁻¹ : ℂ) * h4
  have hsplit : ∀ x, ‖x‖ ^ 2 = ‖P x‖ ^ 2 + ‖M x‖ ^ 2 := by
    intro x
    have horth : inner ℂ (P x) (M x) = 0 :=
      hEO (P x) (M x) (hPeven x) (hModd x)
    calc ‖x‖ ^ 2 = ‖P x + M x‖ ^ 2 := by rw [hPM]
      _ = ‖P x‖ ^ 2 + 2 * (inner ℂ (P x) (M x)).re + ‖M x‖ ^ 2 := by
          exact_mod_cast norm_add_sq (𝕜 := ℂ) (P x) (M x)
      _ = ‖P x‖ ^ 2 + ‖M x‖ ^ 2 := by rw [horth]; simp
  have hqm2 : ‖M q‖ ^ 2 = η := by
    rw [hη]
  have hqp2 : ‖P q‖ ^ 2 = 1 - η := by
    have h := hsplit q
    rw [hq, hqm2] at h
    nlinarith [h]
  have hqpnorm : ‖P q‖ = Real.sqrt (1 - η) := by
    rw [← hqp2, Real.sqrt_sq (norm_nonneg _)]
  have hqmnorm : ‖M q‖ = Real.sqrt η := by
    rw [← hqm2, Real.sqrt_sq (norm_nonneg _)]
  set vp : V := P v with hvp
  set vm : V := M v with hvm
  set γ : ℂ := inner ℂ (P q) vp with hγdef
  have horthqv : γ = -(inner ℂ (M q) vm) := by
    have hqd : inner ℂ q v =
        inner ℂ (P q + M q) (vp + vm) := by
      rw [hPM, hvp, hvm, hPM]
    rw [inner_add_left, inner_add_right, inner_add_right] at hqd
    have h1 : inner ℂ (P q) vm = 0 := hEO _ _ (hPeven q) (hModd v)
    have h2 : inner ℂ (M q) vp = 0 := by
      have h3 := hEO vp (M q) (hPeven v) (hModd q)
      rw [← inner_conj_symm, h3, map_zero]
    rw [h1, h2, hv] at hqd
    rw [hγdef]
    linear_combination -hqd
  have hγbound : ‖γ‖ ≤ Real.sqrt η * ‖vm‖ := by
    rw [horthqv, norm_neg]
    calc ‖inner ℂ (M q) vm‖ ≤ ‖M q‖ * ‖vm‖ := norm_inner_le_norm (𝕜 := ℂ) _ _
      _ = Real.sqrt η * ‖vm‖ := by rw [hqmnorm]
  set u : V := (γ / ((1 - η : ℝ) : ℂ)) • P q with hu
  set w : V := vp - u with hw
  have h1ηℂ : ((1 - η : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr h1η.ne'
  have hqpinner : inner ℂ (P q) (P q) = ((1 - η : ℝ) : ℂ) := by
    rw [← hqp2]
    exact_mod_cast inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (P q)
  have hworth : inner ℂ (P q) w = 0 := by
    have h1 : inner ℂ (P q) u = γ := by
      rw [hu, inner_smul_right, hqpinner, div_mul_cancel₀ _ h1ηℂ]
    rw [hw, inner_sub_right, h1, hγdef]
    exact sub_self _
  have hweven : T w = w := by
    rw [hw]
    have h1 : T vp = vp := hPeven v
    have h2 : T u = u := by
      rw [hu, hTsmul, hPeven]
    calc T (vp - u) = T (vp + -u) := by rw [sub_eq_add_neg]
      _ = T vp + T (-u) := hTadd _ _
      _ = T vp + -(T u) := by
          congr 1
          have h3 := hTsmul (-1 : ℂ) u
          simpa using h3
      _ = vp - u := by rw [h1, h2, sub_eq_add_neg]
  have huw : inner ℂ u w = 0 := by
    rw [hu, inner_smul_left, hworth, mul_zero]
  set d : ℝ := ‖u‖ with hd
  have hd0 : (0:ℝ) ≤ d := hd ▸ norm_nonneg u
  have hdval : d = ‖γ‖ / Real.sqrt (1 - η) := by
    have h1 : d = ‖γ‖ / (1 - η) * Real.sqrt (1 - η) := by
      rw [hd, hu, norm_smul, hqpnorm, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos h1η]
    rw [h1, div_mul_eq_mul_div, div_eq_div_iff h1η.ne' hsq1η.ne',
      mul_assoc, Real.mul_self_sqrt h1η.le]
  have hvpsplit : ‖vp‖ ^ 2 = d ^ 2 + ‖w‖ ^ 2 := by
    have h1 : vp = u + w := by rw [hw]; abel
    rw [h1]
    have h2 := norm_add_sq (𝕜 := ℂ) u w
    rw [huw] at h2
    have h3 : ‖u + w‖ ^ 2 = ‖u‖ ^ 2 + ‖w‖ ^ 2 := by
      simpa using h2
    rw [h3, hd]
  have hγ2 : ‖γ‖ ^ 2 ≤ η * ‖vm‖ ^ 2 := by
    have h := mul_le_mul hγbound hγbound (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    calc ‖γ‖ ^ 2 = ‖γ‖ * ‖γ‖ := by ring
      _ ≤ (Real.sqrt η * ‖vm‖) * (Real.sqrt η * ‖vm‖) := h
      _ = (Real.sqrt η * Real.sqrt η) * (‖vm‖ * ‖vm‖) := by ring
      _ = η * ‖vm‖ ^ 2 := by
          rw [Real.mul_self_sqrt hη0]
          ring
  have hd2γ : d ^ 2 = ‖γ‖ ^ 2 / (1 - η) := by
    rw [hdval, div_pow, Real.sq_sqrt h1η.le]
  have hvsplit : ‖v‖ ^ 2 = ‖vp‖ ^ 2 + ‖vm‖ ^ 2 := hsplit v
  have hdkey : d ^ 2 ≤ η * ‖v‖ ^ 2 := by
    have hvm2 : ‖vm‖ ^ 2 ≤ ‖v‖ ^ 2 - d ^ 2 := by
      have hw2 : 0 ≤ ‖w‖ ^ 2 := by positivity
      nlinarith [hvsplit, hvpsplit]
    have h1 : d ^ 2 * (1 - η) ≤ η * ‖vm‖ ^ 2 := by
      rw [hd2γ, div_mul_cancel₀ _ h1η.ne']
      exact hγ2
    nlinarith
  have hdle : d ≤ Real.sqrt η * ‖v‖ := by
    calc d = Real.sqrt (d ^ 2) := by
          rw [Real.sqrt_sq hd0]
      _ ≤ Real.sqrt (η * ‖v‖ ^ 2) := Real.sqrt_le_sqrt hdkey
      _ = Real.sqrt η * ‖v‖ := by
          rw [Real.sqrt_mul hη0, Real.sqrt_sq (norm_nonneg v)]
  have hwle : ‖w‖ ≤ ‖v‖ := by
    have h1 : ‖w‖ ^ 2 ≤ ‖v‖ ^ 2 := by
      have hd2 : 0 ≤ d ^ 2 := by positivity
      have hvm2 : 0 ≤ ‖vm‖ ^ 2 := by positivity
      nlinarith [hvsplit, hvpsplit]
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (norm_nonneg w), Real.sqrt_sq (norm_nonneg v)] at h2
  have hSqsplit : S q = S (P q) + S (M q) := by
    conv_lhs => rw [← hPM q]
    exact hSadd _ _
  have hSPq_even : T (S (P q)) = S (P q) := by
    rw [← hST, hPeven]
  have hSMq_odd : T (S (M q)) = -(S (M q)) := by
    rw [← hST, hModd]
    have h1 := hSsmul (-1 : ℂ) (M q)
    simpa using h1
  have hSqp_le : ‖S (P q)‖ ≤ ρ := by
    have horth : inner ℂ (S (P q)) (S (M q)) = 0 :=
      hEO _ _ hSPq_even hSMq_odd
    have hpyth : ‖S q‖ ^ 2 = ‖S (P q)‖ ^ 2 + ‖S (M q)‖ ^ 2 := by
      rw [hSqsplit]
      have h1 := norm_add_sq (𝕜 := ℂ) (S (P q)) (S (M q))
      rw [horth] at h1
      simpa using h1
    have h1 : ‖S (P q)‖ ^ 2 ≤ ρ ^ 2 := by
      have h2 : ‖S q‖ ^ 2 ≤ ρ ^ 2 := by
        have h3 := mul_le_mul hρ hρ (norm_nonneg _) hρ0
        calc ‖S q‖ ^ 2 = ‖S q‖ * ‖S q‖ := by ring
          _ ≤ ρ * ρ := h3
          _ = ρ ^ 2 := by ring
      nlinarith [sq_nonneg ‖S (M q)‖]
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hρ0] at h2
  have hSu_le : ‖S u‖ ≤ d * ρ / Real.sqrt (1 - η) := by
    rw [hu, hSsmul, norm_smul, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos h1η]
    calc ‖γ‖ / (1 - η) * ‖S (P q)‖ ≤ ‖γ‖ / (1 - η) * ρ := by
          apply mul_le_mul_of_nonneg_left hSqp_le
          positivity
      _ = d * ρ / Real.sqrt (1 - η) := by
          rw [hdval, div_mul_eq_mul_div, div_mul_eq_mul_div, div_div,
            Real.mul_self_sqrt h1η.le]
  have hcross : (inner ℂ v (S v)).re =
      (inner ℂ vp (S vp)).re + (inner ℂ vm (S vm)).re := by
    have hSv : S v = S vp + S vm := by
      conv_lhs => rw [← hPM v]
      exact hSadd _ _
    have hvd : v = vp + vm := (hPM v).symm
    calc (inner ℂ v (S v)).re
        = (inner ℂ (vp + vm) (S vp + S vm)).re := by rw [← hvd, ← hSv]
      _ = (inner ℂ vp (S vp) + inner ℂ vp (S vm) +
            inner ℂ vm (S vp) + inner ℂ vm (S vm)).re := by
          rw [inner_add_left, inner_add_right, inner_add_right]
          ring_nf
      _ = (inner ℂ vp (S vp)).re + (inner ℂ vm (S vm)).re := by
          have h1 : inner ℂ vp (S vm) = 0 := by
            apply hEO
            · exact hPeven v
            · rw [← hST, hModd]
              have h2 := hSsmul (-1 : ℂ) (M v)
              simpa [hvm] using h2
          have h2 : inner ℂ vm (S vp) = 0 := by
            have h3 : inner ℂ (S vp) vm = 0 := by
              apply hEO
              · rw [← hST, hPeven]
              · exact hModd v
            rw [← inner_conj_symm, h3, map_zero]
          rw [h1, h2]
          simp
  have hoddE : βm * ‖vm‖ ^ 2 ≤ (inner ℂ vm (S vm)).re :=
    hodd vm (hModd v)
  have hre_ge : ∀ z : ℂ, -(‖z‖) ≤ z.re := by
    intro z
    have h1 := abs_le.mp (RCLike.abs_re_le_norm (K := ℂ) z)
    simpa using h1.1
  have hevenE : βp * ‖w‖ ^ 2 ≤ (inner ℂ w (S w)).re :=
    heven w hweven hworth
  have hvpE : (inner ℂ vp (S vp)).re ≥
      βp * ‖w‖ ^ 2 -
        (d * ρ / Real.sqrt (1 - η)) * (d + 2 * ‖w‖) := by
    have hvpuw : vp = u + w := by rw [hw]; abel
    have hSvp : S vp = S u + S w := by
      rw [hvpuw]
      exact hSadd _ _
    have hSu0 : (0:ℝ) ≤ d * ρ / Real.sqrt (1 - η) := by positivity
    have h1 : -(d * (d * ρ / Real.sqrt (1 - η))) ≤
        (inner ℂ u (S u)).re := by
      refine le_trans ?_ (hre_ge _)
      have h2 : ‖inner ℂ u (S u)‖ ≤ d * (d * ρ / Real.sqrt (1 - η)) := by
        calc ‖inner ℂ u (S u)‖ ≤ ‖u‖ * ‖S u‖ := norm_inner_le_norm (𝕜 := ℂ) _ _
          _ ≤ d * (d * ρ / Real.sqrt (1 - η)) := by
              rw [← hd]
              exact mul_le_mul_of_nonneg_left hSu_le hd0
      linarith
    have h2 : -((d * ρ / Real.sqrt (1 - η)) * ‖w‖) ≤
        (inner ℂ u (S w)).re := by
      refine le_trans ?_ (hre_ge _)
      have h3 : ‖inner ℂ u (S w)‖ ≤ (d * ρ / Real.sqrt (1 - η)) * ‖w‖ := by
        rw [← hSsym u w]
        calc ‖inner ℂ (S u) w‖ ≤ ‖S u‖ * ‖w‖ := norm_inner_le_norm (𝕜 := ℂ) _ _
          _ ≤ (d * ρ / Real.sqrt (1 - η)) * ‖w‖ :=
              mul_le_mul_of_nonneg_right hSu_le (norm_nonneg _)
      linarith
    have h3 : -((d * ρ / Real.sqrt (1 - η)) * ‖w‖) ≤
        (inner ℂ w (S u)).re := by
      refine le_trans ?_ (hre_ge _)
      have h4 : ‖inner ℂ w (S u)‖ ≤ (d * ρ / Real.sqrt (1 - η)) * ‖w‖ := by
        calc ‖inner ℂ w (S u)‖ ≤ ‖w‖ * ‖S u‖ := norm_inner_le_norm (𝕜 := ℂ) _ _
          _ ≤ ‖w‖ * (d * ρ / Real.sqrt (1 - η)) :=
              mul_le_mul_of_nonneg_left hSu_le (norm_nonneg _)
          _ = (d * ρ / Real.sqrt (1 - η)) * ‖w‖ := by ring
      linarith
    have hre : (inner ℂ vp (S vp)).re =
        (inner ℂ u (S u)).re + (inner ℂ u (S w)).re +
          (inner ℂ w (S u)).re + (inner ℂ w (S w)).re := by
      rw [hSvp, hvpuw, inner_add_left, inner_add_right, inner_add_right]
      simp [Complex.add_re]
      ring
    rw [hre]
    nlinarith [hevenE]
  have hmβp : min βp βm ≤ βp := min_le_left _ _
  have hmβm : min βp βm ≤ βm := min_le_right _ _
  have hsum : (inner ℂ v (S v)).re ≥
      min βp βm * (‖vm‖ ^ 2 + ‖w‖ ^ 2) -
        (ρ / Real.sqrt (1 - η)) * (d ^ 2 + 2 * d * ‖w‖) := by
    rw [hcross]
    have h1 : min βp βm * ‖vm‖ ^ 2 ≤ βm * ‖vm‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hmβm (by positivity)
    have h2 : min βp βm * ‖w‖ ^ 2 ≤ βp * ‖w‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hmβp (by positivity)
    have h3 : (d * ρ / Real.sqrt (1 - η)) * (d + 2 * ‖w‖) =
        (ρ / Real.sqrt (1 - η)) * (d ^ 2 + 2 * d * ‖w‖) := by
      ring
    nlinarith [hvpE, hoddE]
  have hnormsum : ‖vm‖ ^ 2 + ‖w‖ ^ 2 = ‖v‖ ^ 2 - d ^ 2 := by
    linarith [hvsplit, hvpsplit]
  exact real_assembly βp βm η ρ betaEff ‖v‖ ‖w‖ ‖vm‖ d
    ((inner ℂ v (S v)).re) hη0 hη1 hρ0 hbeta hbeta0
    (norm_nonneg v) (norm_nonneg w) (norm_nonneg vm) hd0
    hdkey hdle hwle hnormsum hsum

/-! ## The public matrix theorem -/

/-- **H2a.1.**  Reflection sector floors, odd mass and residual control give
the full literal complement floor: on a finite complex carrier, a Hermitian
`K` commuting with a Hermitian unitary involution `J`, a unit trial `q`
with odd mass `η < 1` and residual bound `ρ` at the real shift `a`, and
sector floors `βp` (even sector, orthogonally to the even part of `q`) and
`βm` (odd sector) yield `complexTrialComplementFloor K q a betaEff` with
`betaEff = min(βp,βm)*(1-η) - ((2*√η+η)/√(1-η))*ρ`.  Exact trial parity is
neither assumed nor concluded. -/
theorem complexTrialComplementFloor_of_reflectionSectorFloors_oddMass_residual
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K J : Matrix ι ι ℂ) (q : ι → ℂ) (a η βp βm ρ betaEff : ℝ)
    (hK : K.IsHermitian) (hJ : J.IsHermitian) (hJ2 : J * J = 1)
    (hKJ : K * J = J * K)
    (hq : star q ⬝ᵥ q = 1)
    (hη : η = (star ((2⁻¹ : ℂ) • (q - J *ᵥ q)) ⬝ᵥ
      ((2⁻¹ : ℂ) • (q - J *ᵥ q))).re)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (heven : ∀ x : ι → ℂ, J *ᵥ x = x →
      star ((2⁻¹ : ℂ) • (q + J *ᵥ q)) ⬝ᵥ x = 0 →
      βp * (star x ⬝ᵥ x).re ≤
        (star x ⬝ᵥ ((K - (a : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ x)).re)
    (hodd : ∀ x : ι → ℂ, J *ᵥ x = -x →
      βm * (star x ⬝ᵥ x).re ≤
        (star x ⬝ᵥ ((K - (a : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ x)).re)
    (hρ0 : 0 ≤ ρ)
    (hρ : (star ((K - (a : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ q) ⬝ᵥ
      ((K - (a : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ q)).re ≤ ρ ^ 2)
    (hbeta : betaEff = min βp βm * (1 - η) -
      (2 * Real.sqrt η + η) / Real.sqrt (1 - η) * ρ)
    (hbeta0 : 0 < betaEff) :
    complexTrialComplementFloor K q (a : ℂ) betaEff := by
  classical
  set Sm : Matrix ι ι ℂ := K - (a : ℂ) • (1 : Matrix ι ι ℂ) with hSm
  have hSherm : Sm.IsHermitian := by
    rw [hSm]
    show (K - (a : ℂ) • (1 : Matrix ι ι ℂ))ᴴ = _
    rw [Matrix.conjTranspose_sub, hK.eq, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one]
    congr 1
    simp [Complex.star_def, Complex.conj_ofReal]
  have hdotSym : ∀ (N : Matrix ι ι ℂ), N.IsHermitian →
      ∀ x y : ι → ℂ, star (N *ᵥ x) ⬝ᵥ y = star x ⬝ᵥ (N *ᵥ y) := by
    intro N hN x y
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hN.eq]
  -- the pointwise core on the q-orthogonal complement
  have hcore : ∀ v : ι → ℂ, star q ⬝ᵥ v = 0 →
      betaEff * (star v ⬝ᵥ v).re ≤ (star v ⬝ᵥ (Sm *ᵥ v)).re := by
    intro v hv
    have h := core_contamination_bound
      (V := EuclideanSpace ℂ ι)
      (S := fun x => WithLp.toLp 2 (Sm *ᵥ WithLp.ofLp x))
      (T := fun x => WithLp.toLp 2 (J *ᵥ WithLp.ofLp x))
      (fun x y => by
        simp [Matrix.mulVec_add])
      (fun c x => by
        simp [Matrix.mulVec_smul])
      (fun x y => by
        rw [← dot_eq_inner, ← dot_eq_inner]
        exact hdotSym Sm hSherm _ _)
      (fun x y => by
        simp [Matrix.mulVec_add])
      (fun c x => by
        simp [Matrix.mulVec_smul])
      (fun x y => by
        rw [← dot_eq_inner, ← dot_eq_inner]
        exact hdotSym J hJ _ _)
      (fun x => by
        simp only [WithLp.ofLp_toLp]
        rw [Matrix.mulVec_mulVec, hJ2, Matrix.one_mulVec])
      (fun x => by
        simp only [WithLp.ofLp_toLp]
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
        congr 1
        rw [hSm, Matrix.sub_mul, Matrix.mul_sub, hKJ,
          Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
          Matrix.mul_one])
      (WithLp.toLp 2 q)
      (by
        have h1 := dot_self_re_eq_norm_sq q
        rw [hq] at h1
        have h2 : ‖(WithLp.toLp 2 q : EuclideanSpace ℂ ι)‖ ^ 2 = 1 := by
          rw [← h1]
          norm_num
        nlinarith [norm_nonneg (WithLp.toLp 2 q : EuclideanSpace ℂ ι)])
      η βp βm ρ betaEff
      (by
        rw [hη]
        have h1 := dot_self_re_eq_norm_sq ((2⁻¹ : ℂ) • (q - J *ᵥ q))
        rw [h1]
        congr 1)
      hη1
      (fun x hx horth => by
        have h1 := heven (WithLp.ofLp x)
          (by
            have h2 := congrArg (WithLp.ofLp) hx
            simpa using h2)
          (by
            rw [dot_eq_inner]
            convert horth using 2)
        rw [dot_self_re_eq_norm_sq, dot_eq_inner] at h1
        convert h1 using 2)
      (fun x hx => by
        have h1 := hodd (WithLp.ofLp x)
          (by
            have h2 := congrArg (WithLp.ofLp) hx
            simpa using h2)
        rw [dot_self_re_eq_norm_sq, dot_eq_inner] at h1
        convert h1 using 2)
      hρ0
      (by
        have h1 := dot_self_re_eq_norm_sq (Sm *ᵥ q)
        rw [h1] at hρ
        have h2 := Real.sqrt_le_sqrt hρ
        rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hρ0] at h2
        convert h2 using 2)
      hbeta hbeta0
      (WithLp.toLp 2 v)
      (by
        rw [← dot_eq_inner]
        exact hv)
    rw [dot_self_re_eq_norm_sq, dot_eq_inner]
    convert h using 2
  -- projector plumbing (local copies of the private upstream helpers)
  have hQvec : ∀ x : ι → ℂ,
      complexTrialLineComplement q *ᵥ x = x - (star q ⬝ᵥ x) • q := by
    intro x
    rw [complexTrialLineComplement, Matrix.sub_mulVec, Matrix.one_mulVec]
    congr 1
    ext j
    simp [complexTrialLineProjection, Matrix.mulVec, Matrix.vecMulVec_apply,
      dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
  have hQperp : ∀ x : ι → ℂ,
      star q ⬝ᵥ (complexTrialLineComplement q *ᵥ x) = 0 := by
    intro x
    rw [hQvec, dotProduct_sub, dotProduct_smul, hq, smul_eq_mul, mul_one,
      sub_self]
  have hQherm : (complexTrialLineComplement q).IsHermitian := by
    show (complexTrialLineComplement q)ᴴ = complexTrialLineComplement q
    rw [complexTrialLineComplement, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one]
    congr 1
    show (complexTrialLineProjection q)ᴴ = complexTrialLineProjection q
    rw [complexTrialLineProjection, Matrix.conjTranspose_vecMulVec, star_star]
  have hQidem : ∀ x : ι → ℂ,
      complexTrialLineComplement q *ᵥ (complexTrialLineComplement q *ᵥ x) =
        complexTrialLineComplement q *ᵥ x := by
    intro x
    rw [hQvec (complexTrialLineComplement q *ᵥ x), hQperp, zero_smul,
      sub_zero]
  refine ⟨hbeta0, fun x => ?_⟩
  have hBv : (complexTrialLineComplement q *
      (K - (a : ℂ) • (1 : Matrix ι ι ℂ)) *
      complexTrialLineComplement q) *ᵥ x =
      complexTrialLineComplement q *ᵥ
        (Sm *ᵥ (complexTrialLineComplement q *ᵥ x)) := by
    rw [hSm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hBv]
  have htransfer :
      star (complexTrialLineComplement q *ᵥ x) ⬝ᵥ
        (complexTrialLineComplement q *ᵥ
          (Sm *ᵥ (complexTrialLineComplement q *ᵥ x))) =
      star (complexTrialLineComplement q *ᵥ x) ⬝ᵥ
        (Sm *ᵥ (complexTrialLineComplement q *ᵥ x)) := by
    rw [← hdotSym _ hQherm, hQidem]
  rw [htransfer]
  exact hcore (complexTrialLineComplement q *ᵥ x) (hQperp x)

#print axioms oddMass_without_residual_control_does_not_force_complementFloor_plant
#print axioms complexTrialComplementFloor_of_reflectionSectorFloors_oddMass_residual

end Q3.RouteB

end
