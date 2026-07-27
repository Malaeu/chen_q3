import RequestProject.Main

/-!
# H2a bridge layer: spectral-data content and transport

This file connects the proved finite pencil engine
`H2aPenalty.H2a_SimpleEvenGround_FromPenaltyCoercivity` to the RH-route spectral
data `RHRoute.SpectralData`, via the structures `RHRoute.PencilData` and
`RHRoute.PencilBridge` introduced in `RequestProject.Main`.

* `ground_simple_isolated_even_of_spectralData` (T1): from `SpectralData P j`,
  the underlying pencil has a lowest eigenvalue `lam ≤ a`, spectral gap `β - a`,
  one-dimensional lowest eigenspace, and every lowest eigenvector is `J`-even.
* `hfam_even_of_spectralData` (T2): from `SpectralData P j`, the approximant
  `Hfam P j` is an even function.
* `wrong_parity_blocks_evenness` (T3): a `Fin 2` counterexample satisfying every
  `PencilData` field except `hJK`, whose lowest eigenvector is not `J`-even.
-/

open Matrix
open scoped ComplexOrder

namespace RHRoute

/-- **T1.**  From `SpectralData P j`, the underlying finite Hermitian pencil `(K, G)`
has a lowest generalized eigenvalue `lam ≤ a` that is the minimum of the spectrum,
with spectral gap `β - a` (every other eigenvalue `μ` satisfies `β - a ≤ μ - lam`),
a one-dimensional lowest eigenspace, and every lowest eigenvector `J`-even.  This is
a direct application of `H2aPenalty.H2a_SimpleEvenGround_FromPenaltyCoercivity`. -/
theorem ground_simple_isolated_even_of_spectralData (P : Approx) (j : ℕ)
    (h : SpectralData P j) :
    ∃ (D : PencilData) (lam : ℝ),
      Nonempty (PencilBridge P j D) ∧
      (∃ x, H2aPenalty.GEig D.K D.G lam x) ∧
      lam ≤ D.a ∧
      (∀ μ y, H2aPenalty.GEig D.K D.G μ y → lam ≤ μ) ∧
      (∀ μ y, H2aPenalty.GEig D.K D.G μ y → μ ≠ lam → D.β - D.a ≤ μ - lam) ∧
      (∀ x y, H2aPenalty.GEig D.K D.G lam x → H2aPenalty.GEig D.K D.G lam y →
        ∃ c : ℂ, y = c • x) ∧
      (∀ x, H2aPenalty.GEig D.K D.G lam x → D.J *ᵥ x = x) := by
  obtain ⟨D, hb⟩ := h.content
  obtain ⟨lam, hlam⟩ :=
    H2aPenalty.H2a_SimpleEvenGround_FromPenaltyCoercivity D.G D.K D.J D.q D.a D.β D.τ
      D.hG D.hK D.hJ D.hJG D.hJK D.hJq D.hq D.ha D.hab D.hcert
  exact ⟨D, lam, hb, hlam.1, hlam.2.1, hlam.2.2.1, hlam.2.2.2.1, hlam.2.2.2.2.1,
    hlam.2.2.2.2.2⟩

/-- **T2.**  From `SpectralData P j`, the approximant `Hfam P j` is an even function:
`Hfam P j z = Hfam P j (-z)` for all `z`.  Route: take a lowest eigenvector `x`
(existence from the engine), use its `J`-evenness `J x = x`, the bridge's
`parity_intertwine` and `ground_link`, and linearity. -/
theorem hfam_even_of_spectralData (P : Approx) (j : ℕ) (h : SpectralData P j) :
    ∀ z, Hfam P j z = Hfam P j (-z) := by
  obtain ⟨D, ⟨B⟩⟩ := h.content
  obtain ⟨lam, hlam⟩ :=
    H2aPenalty.H2a_SimpleEvenGround_FromPenaltyCoercivity D.G D.K D.J D.q D.a D.β D.τ
      D.hG D.hK D.hJ D.hJG D.hJK D.hJq D.hq D.ha D.hab D.hcert
  obtain ⟨x, hx⟩ := hlam.1
  have hlowest := hlam.2.2.1
  have heven : D.J *ᵥ x = x := hlam.2.2.2.2.2 x hx
  obtain ⟨c, _hc_ne, hc⟩ := B.ground_link lam x hx hlowest
  have hpar := B.parity_intertwine x
  rw [heven] at hpar
  intro z
  rw [hc z, hc (-z), congrFun hpar z]

/-
**T3 (plant / counterexample).**  Pencil data over `Fin 2` satisfying every
`PencilData` field **except** `hJK` (`Jᴴ * K * J = K`), for which some lowest
eigenvector is not `J`-even.  Concretely `G = diag(1,2)`, `K = !![0,6; 6,14]`,
`J = diag(1,-1)`, `q = ![1,0]`, `a = 0`, `β = 2`, `τ = 6`; the lowest generalized
eigenvalue is `-2` with eigenvector `![3,-1]`, which is not fixed by `J`.  This shows
`hJK` is load-bearing for the evenness conclusion.
-/
theorem wrong_parity_blocks_evenness :
    ∃ (G K J : Matrix (Fin 2) (Fin 2) ℂ) (q : Fin 2 → ℂ) (a β τ : ℝ),
      G.PosDef ∧ K.IsHermitian ∧ J * J = 1 ∧ Jᴴ * G * J = G ∧
      J *ᵥ q = q ∧ star q ⬝ᵥ (G *ᵥ q) = 1 ∧ star q ⬝ᵥ (K *ᵥ q) = (a : ℂ) ∧ a < β ∧
      (K - (β : ℂ) • G + (τ : ℂ) • Matrix.vecMulVec (G *ᵥ q) (star (G *ᵥ q))).PosSemidef ∧
      ¬ (Jᴴ * K * J = K) ∧
      (∃ (lam : ℝ) (x : Fin 2 → ℂ),
        H2aPenalty.GEig K G lam x ∧
        (∀ μ y, H2aPenalty.GEig K G μ y → lam ≤ μ) ∧
        J *ᵥ x ≠ x) := by
  refine' ⟨ Matrix.diagonal ( fun i => if i = 0 then 1 else 2 ), !![0, 6; 6, 14], Matrix.diagonal ( fun i => if i = 0 then 1 else -1 ), ![1, 0], 0, 2, 6, _, _, _, _, _ ⟩ <;> norm_num;
  · ext i j ; fin_cases i <;> fin_cases j <;> norm_num;
  · ext i j ; aesop;
  · refine' ⟨ _, _, _, _, _ ⟩ <;> norm_num [ ← List.ofFn_inj, Matrix.mulVec ];
    · convert Matrix.posSemidef_conjTranspose_mul_self _ using 1;
      rotate_left;
      exact Fin 2;
      all_goals try infer_instance;
      exact Matrix.of ![![2, 3], ![0, 1]];
      ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ Matrix.vecMulVec, Matrix.mulVec ];
      · norm_num [ Matrix.mul_apply ];
        norm_num [ Complex.ext_iff ];
      · norm_num [ Matrix.mul_apply ];
        norm_num [ Complex.ext_iff ];
      · norm_num [ Matrix.mul_apply, Matrix.conjTranspose ];
        norm_num [ Complex.ext_iff ];
      · norm_num [ Matrix.mul_apply ];
        norm_num [ Complex.ext_iff ];
    · intro h; have := congr_fun ( congr_fun h 0 ) 1; norm_num [ Matrix.mul_apply ] at this;
    · refine' ⟨ -2, fun i => if i = 0 then 3 else -1, _, _, _ ⟩ <;> norm_num [ H2aPenalty.GEig ];
      · norm_num [ funext_iff, Fin.forall_fin_two, vecHead, vecTail, Matrix.mulVec ];
      · intro μ y hy hμ; have := congr_fun hμ 0; have := congr_fun hμ 1; simp_all +decide [ funext_iff, Fin.forall_fin_two, Matrix.mulVec ] ;
        by_cases h : y 0 = 0 <;> simp_all +decide [ vecHead, vecTail ];
        -- Substitute y 1 from the first equation into the second equation.
        have h_sub : 6 * y 0 + 14 * ((μ * y 0) / 6) = μ * (2 * ((μ * y 0) / 6)) := by
          grind;
        -- Simplify the equation $6 * y 0 + 14 * (μ * y 0 / 6) = μ * (2 * (μ * y 0 / 6))$ to get $36 + 14μ = 2μ^2$.
        have h_simplified : 36 + 14 * μ = 2 * μ^2 := by
          exact_mod_cast ( mul_left_cancel₀ h <| by linear_combination' h_sub * 6 : ( 36 : ℂ ) + 14 * μ = 2 * μ ^ 2 );
        nlinarith

end RHRoute