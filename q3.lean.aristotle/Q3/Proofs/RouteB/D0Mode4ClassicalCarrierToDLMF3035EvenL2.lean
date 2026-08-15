import Q3.Proofs.RouteB.D0Mode4DLMF3035EvenL2ToFiniteLimitSpectrum
import Q3.Proofs.RouteB.D0Mode4ClassicalCarrierHeadUpper

/-!
# Finite-limit carrier values below twenty give the DLMF l2 row

This leaf closes the singular-endpoint wall isolated by the 2026-08-15 Goal
058 Proshka judgment.  If a fixed-index finite DLMF eigenvalue converges to
`Λ < 20`, then the literal Hermitian Schur matrix at `Λ` must be singular.
Otherwise local stability would give equal negative counts immediately below
and above `Λ`, while convergence of that same finite index forces those counts
to differ by at least one.

The determinant identity then gives the exact root, the source-locked DLMF
30.3.5 characteristic equation, and the normalized square-summable left row.
This remains a spectral-source theorem only: it does not identify a particular
degree-four index, prove endpoint counts, promote Route B, or claim RH.

Knowledge preflight receipt: the pre-admission deep query
`mode4ClassicalEvenEigenvalue literal Schur determinant zero below twenty
carrier singular endpoint` completed all eight registered shelves and the
enabled `zeta23` base.  It found no pre-existing Lean supplier at HEAD
`c0f990a9`; the only exact target-name occurrences there were textual records
of the Proshka wall.  The current worktree theorem was not treated as an
independent supplier.
-/

open Filter Topology

namespace Q3.RouteB

noncomputable section

private theorem mode4HermitianSchurMatrix_continuousAt_lambda
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ < 20) :
    ContinuousAt
      (fun t : ℝ => mode4HermitianSchurMatrix mProject t K) Λ := by
  have htail :
      ContinuousAt (fun t : ℝ => mode4RightTailLimit mProject t K) Λ :=
    (mode4RightTailLimit_continuousOn_lambda
      mProject K hm hK hsep).continuousAt (Iic_mem_nhds hΛ)
  have hsub :
      (fun t : ℝ =>
        mode4HermitianSchurMatrix mProject t K -
          mode4HermitianSchurMatrix mProject Λ K) =
      (fun t : ℝ =>
        (Λ - t) • (1 : Matrix (Fin K) (Fin K) ℝ) +
          Matrix.diagonal (fun i : Fin K =>
            if i.val = 0 then
              mode4JacobiUpper (mode4JacobiG mProject) (K - 1) *
                (mode4RightTailLimit mProject Λ K -
                  mode4RightTailLimit mProject t K)
            else 0)) := by
    funext t
    exact mode4HermitianSchurMatrix_sub_eq_smul_one_add_diagonal
      mProject K t Λ (by omega)
  have hsubContinuous :
      ContinuousAt
        (fun t : ℝ =>
          mode4HermitianSchurMatrix mProject t K -
            mode4HermitianSchurMatrix mProject Λ K) Λ := by
    rw [hsub]
    apply ContinuousAt.add
    · apply continuousAt_pi.2
      intro i
      apply continuousAt_pi.2
      intro j
      simp only [Matrix.smul_apply]
      fun_prop
    · apply continuousAt_pi.2
      intro i
      apply continuousAt_pi.2
      intro j
      by_cases hij : i = j
      · subst j
        simp only [Matrix.diagonal_apply_eq]
        by_cases hi : i.val = 0
        · simp only [hi, if_true]
          exact continuousAt_const.mul (continuousAt_const.sub htail)
        · simp only [hi, if_false]
          exact continuousAt_const
      · simp only [Matrix.diagonal_apply_ne _ hij]
        exact continuousAt_const
  have hadd := hsubContinuous.add
    (continuousAt_const :
      ContinuousAt
        (fun _ : ℝ => mode4HermitianSchurMatrix mProject Λ K) Λ)
  simpa only [sub_add_cancel] using hadd

private def mode4CarrierDepth
    (K j : ℕ) (d : ℕ) : {D : ℕ // j < D} :=
  ⟨K + (j + 1 + d), by omega⟩

private theorem mode4CarrierDepth_tendsto
    (K j : ℕ) :
    Filter.Tendsto (mode4CarrierDepth K j) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨b.1, ?_⟩
  intro d hd
  change b.1 ≤ K + (j + 1 + d)
  omega

private theorem mode4NatShift_tendsto (c : ℕ) :
    Filter.Tendsto (fun d : ℕ => c + d) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨b, ?_⟩
  intro d hd
  omega

private theorem mode4CarrierEigenvalue_tendsto_along_schurDepth
    (G : ℝ) (K j : ℕ) (hG : 0 < G) :
    Filter.Tendsto
      (fun d : ℕ =>
        mode4DLMFEvenFiniteEigenvalue G (K + (j + 1 + d))
          ⟨j, by omega⟩)
      Filter.atTop (nhds (mode4ClassicalEvenEigenvalue G j)) := by
  simpa [mode4CarrierDepth] using
    (mode4ClassicalEvenEigenvalue_tendsto G j hG).comp
      (mode4CarrierDepth_tendsto K j)

private theorem mode4Card_filter_lt_ge_succ_of_monotone'
    {d : ℕ} (f : Fin d → ℝ) (hf : Monotone f)
    (p : Fin d) (t : ℝ) (hpt : f p < t) :
    p.val + 1 ≤ (Finset.univ.filter fun i => f i < t).card := by
  have hsub : Finset.Iic p ⊆ Finset.univ.filter (fun i => f i < t) := by
    intro i hi
    rw [Finset.mem_Iic] at hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, lt_of_le_of_lt (hf hi) hpt⟩
  calc
    p.val + 1 = (Finset.Iic p).card := by rw [Fin.card_Iic]
    _ ≤ (Finset.univ.filter fun i => f i < t).card :=
      Finset.card_le_card hsub

private theorem mode4Card_filter_lt_le_of_monotone'
    {d : ℕ} (f : Fin d → ℝ) (hf : Monotone f)
    (p : Fin d) (t : ℝ) (htp : t ≤ f p) :
    (Finset.univ.filter fun i => f i < t).card ≤ p.val := by
  have hsub : Finset.univ.filter (fun i => f i < t) ⊆ Finset.Iio p := by
    intro i hi
    have hit := (Finset.mem_filter.mp hi).2
    rw [Finset.mem_Iio]
    by_contra hnot
    have hpi : p ≤ i := le_of_not_gt hnot
    exact (not_lt_of_ge (le_trans htp (hf hpi))) hit
  calc
    (Finset.univ.filter fun i => f i < t).card ≤ (Finset.Iio p).card :=
      Finset.card_le_card hsub
    _ = p.val := by rw [Fin.card_Iio]

/-- A finite-limit classical even value below twenty is a singular endpoint of
the literal Hermitian Schur family.  This is the local-count contradiction
missing from the previous production direction. -/
theorem
    mode4ClassicalEvenEigenvalue_eq_imp_literalSchur_det_eq_zero_of_lt_twenty
    (mProject K j : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ < 20)
    (hcarrier :
      mode4ClassicalEvenEigenvalue
          (mode4JacobiG mProject) j = Λ) :
    (mode4HermitianSchurMatrix mProject Λ K).det = 0 := by
  by_contra hdetZero
  have hdet : (mode4HermitianSchurMatrix mProject Λ K).det ≠ 0 := hdetZero
  let G := mode4JacobiG mProject
  have hG : 0 < G := by
    unfold G mode4JacobiG
    positivity
  let ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  let Λlo : ℕ → ℝ := fun n => Λ - ε n
  let Λhi : ℕ → ℝ := fun n => Λ + ε n
  have hε : Filter.Tendsto ε Filter.atTop (nhds 0) := by
    simpa [ε] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1))
          Filter.atTop (nhds 0))
  have hlo : Filter.Tendsto Λlo Filter.atTop (nhds Λ) := by
    simpa [Λlo] using (tendsto_const_nhds.sub hε)
  have hhi : Filter.Tendsto Λhi Filter.atTop (nhds Λ) := by
    simpa [Λhi] using (tendsto_const_nhds.add hε)
  have hmatrixContinuous :=
    mode4HermitianSchurMatrix_continuousAt_lambda
      mProject K Λ hm hK hsep hΛ
  have hmatrixLo :
      Filter.Tendsto
        (fun n => mode4HermitianSchurMatrix mProject (Λlo n) K)
        Filter.atTop
        (nhds (mode4HermitianSchurMatrix mProject Λ K)) :=
    hmatrixContinuous.tendsto.comp hlo
  have hmatrixHi :
      Filter.Tendsto
        (fun n => mode4HermitianSchurMatrix mProject (Λhi n) K)
        Filter.atTop
        (nhds (mode4HermitianSchurMatrix mProject Λ K)) :=
    hmatrixContinuous.tendsto.comp hhi
  have hcountLo :=
    mode4HermitianNegativeEigenvalueCount_eventually_eq_of_tendsto_of_det_ne_zero
      (fun n => mode4HermitianSchurMatrix mProject (Λlo n) K)
      (fun n => mode4HermitianSchurMatrix_isHermitian mProject K (Λlo n))
      (mode4HermitianSchurMatrix mProject Λ K)
      (mode4HermitianSchurMatrix_isHermitian mProject K Λ)
      hmatrixLo hdet
  have hcountHi :=
    mode4HermitianNegativeEigenvalueCount_eventually_eq_of_tendsto_of_det_ne_zero
      (fun n => mode4HermitianSchurMatrix mProject (Λhi n) K)
      (fun n => mode4HermitianSchurMatrix_isHermitian mProject K (Λhi n))
      (mode4HermitianSchurMatrix mProject Λ K)
      (mode4HermitianSchurMatrix_isHermitian mProject K Λ)
      hmatrixHi hdet
  have hdetLo :
      ∀ᶠ n : ℕ in Filter.atTop,
        (mode4HermitianSchurMatrix mProject (Λlo n) K).det ≠ 0 :=
    ((continuous_id.matrix_det.tendsto _).comp hmatrixLo).eventually_ne hdet
  have hdetHi :
      ∀ᶠ n : ℕ in Filter.atTop,
        (mode4HermitianSchurMatrix mProject (Λhi n) K).det ≠ 0 :=
    ((continuous_id.matrix_det.tendsto _).comp hmatrixHi).eventually_ne hdet
  have hlo20 : ∀ᶠ n : ℕ in Filter.atTop, Λlo n ≤ 20 :=
    hlo.eventually (Iic_mem_nhds hΛ)
  have hhi20 : ∀ᶠ n : ℕ in Filter.atTop, Λhi n ≤ 20 :=
    hhi.eventually (Iic_mem_nhds hΛ)
  obtain ⟨n, hnCountLo, hnCountHi, hnDetLo, hnDetHi, hnLo20, hnHi20⟩ :=
    (hcountLo.and (hcountHi.and
      (hdetLo.and (hdetHi.and (hlo20.and hhi20))))).exists
  have hεpos : 0 < ε n := by
    dsimp [ε]
    positivity
  have hnLoCarrier : Λlo n < mode4ClassicalEvenEigenvalue G j := by
    rw [hcarrier]
    dsimp [Λlo]
    linarith
  have hnCarrierHi : mode4ClassicalEvenEigenvalue G j < Λhi n := by
    rw [hcarrier]
    dsimp [Λhi]
    linarith
  have htransportLo :=
    mode4ActualFiniteJacobiTruncation_negativeCount_eventually_eq_hermitianSchurMatrix
      mProject K (Λlo n) hm hK hsep hnLo20 hnDetLo
  have htransportHi :=
    mode4ActualFiniteJacobiTruncation_negativeCount_eventually_eq_hermitianSchurMatrix
      mProject K (Λhi n) hm hK hsep hnHi20 hnDetHi
  have hfiniteCountLo :
      ∀ᶠ d : ℕ in Filter.atTop,
        (Finset.univ.filter fun p : Fin (K + (j + 1 + d)) =>
          mode4DLMFEvenFiniteEigenvalue G (K + (j + 1 + d)) p <
            Λlo n).card =
        mode4HermitianNegativeEigenvalueCount
          (mode4HermitianSchurMatrix mProject (Λlo n) K)
          (mode4HermitianSchurMatrix_isHermitian mProject K (Λlo n)) := by
    have hpulled :=
      (mode4NatShift_tendsto (j + 1)).eventually htransportLo
    filter_upwards [hpulled] with d hd
    simpa using
      (mode4ActualFiniteJacobiTruncation_negativeCount_eq_finiteCount
        mProject K (j + 1 + d) (Λlo n)).symm.trans hd
  have hfiniteCountHi :
      ∀ᶠ d : ℕ in Filter.atTop,
        (Finset.univ.filter fun p : Fin (K + (j + 1 + d)) =>
          mode4DLMFEvenFiniteEigenvalue G (K + (j + 1 + d)) p <
            Λhi n).card =
        mode4HermitianNegativeEigenvalueCount
          (mode4HermitianSchurMatrix mProject (Λhi n) K)
          (mode4HermitianSchurMatrix_isHermitian mProject K (Λhi n)) := by
    have hpulled :=
      (mode4NatShift_tendsto (j + 1)).eventually htransportHi
    filter_upwards [hpulled] with d hd
    simpa using
      (mode4ActualFiniteJacobiTruncation_negativeCount_eq_finiteCount
        mProject K (j + 1 + d) (Λhi n)).symm.trans hd
  have hconv :=
    mode4CarrierEigenvalue_tendsto_along_schurDepth G K j hG
  have haboveLo :
      ∀ᶠ d : ℕ in Filter.atTop,
        Λlo n <
          mode4DLMFEvenFiniteEigenvalue G (K + (j + 1 + d))
            ⟨j, by omega⟩ :=
    hconv.eventually_const_lt hnLoCarrier
  have hbelowHi :
      ∀ᶠ d : ℕ in Filter.atTop,
        mode4DLMFEvenFiniteEigenvalue G (K + (j + 1 + d))
            ⟨j, by omega⟩ < Λhi n :=
    hconv.eventually_lt_const hnCarrierHi
  obtain ⟨d, hdCountLo, hdCountHi, hdAboveLo, hdBelowHi⟩ :=
    (hfiniteCountLo.and
      (hfiniteCountHi.and (haboveLo.and hbelowHi))).exists
  have hcardLo := mode4Card_filter_lt_le_of_monotone'
    (mode4DLMFEvenFiniteEigenvalue G (K + (j + 1 + d)))
    (mode4DLMFEvenFiniteEigenvalue_monotone G (K + (j + 1 + d)))
    (⟨j, by omega⟩ : Fin (K + (j + 1 + d))) (Λlo n) hdAboveLo.le
  have hcardHi := mode4Card_filter_lt_ge_succ_of_monotone'
    (mode4DLMFEvenFiniteEigenvalue G (K + (j + 1 + d)))
    (mode4DLMFEvenFiniteEigenvalue_monotone G (K + (j + 1 + d)))
    (⟨j, by omega⟩ : Fin (K + (j + 1 + d))) (Λhi n) hdBelowHi
  have hcountLoLe :
      mode4HermitianNegativeEigenvalueCount
          (mode4HermitianSchurMatrix mProject (Λlo n) K)
          (mode4HermitianSchurMatrix_isHermitian mProject K (Λlo n)) ≤ j := by
    rw [hdCountLo] at hcardLo
    simpa using hcardLo
  have hcountHiGe :
      j + 1 ≤
        mode4HermitianNegativeEigenvalueCount
          (mode4HermitianSchurMatrix mProject (Λhi n) K)
          (mode4HermitianSchurMatrix_isHermitian mProject K (Λhi n)) := by
    rw [hdCountHi] at hcardHi
    simpa using hcardHi
  have hnCountLo' :
      mode4HermitianNegativeEigenvalueCount
          (mode4HermitianSchurMatrix mProject (Λlo n) K)
          (mode4HermitianSchurMatrix_isHermitian mProject K (Λlo n)) =
        mode4HermitianNegativeEigenvalueCount
          (mode4HermitianSchurMatrix mProject Λ K)
          (mode4HermitianSchurMatrix_isHermitian mProject K Λ) := by
    simpa using hnCountLo
  have hnCountHi' :
      mode4HermitianNegativeEigenvalueCount
          (mode4HermitianSchurMatrix mProject (Λhi n) K)
          (mode4HermitianSchurMatrix_isHermitian mProject K (Λhi n)) =
        mode4HermitianNegativeEigenvalueCount
          (mode4HermitianSchurMatrix mProject Λ K)
          (mode4HermitianSchurMatrix_isHermitian mProject K Λ) := by
    simpa using hnCountHi
  rw [hnCountLo'] at hcountLoLe
  rw [hnCountHi'] at hcountHiGe
  omega

/-- Production-domain reverse direction: every finite-limit carrier value
below twenty supplies the normalized square-summable DLMF 30.3.5 even row. -/
theorem
    mode4ClassicalEvenEigenvalue_eq_imp_DLMF3035EvenLeftCoefficient_sqSummable
    (mProject K j : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ < 20)
    (hcarrier :
      mode4ClassicalEvenEigenvalue
          (mode4JacobiG mProject) j = Λ) :
    Summable
      (fun q : ℕ =>
        ‖mode4DLMF3035EvenLeftCoefficient
            (mode4JacobiG mProject) Λ q‖ ^ 2) := by
  have hdet :=
    mode4ClassicalEvenEigenvalue_eq_imp_literalSchur_det_eq_zero_of_lt_twenty
      mProject K j Λ hm hK hsep hΛ hcarrier
  have hroot : mode4RootFunction mProject K Λ = 0 := by
    have hprod :
        mode4JacobiUpperProd (mode4JacobiG mProject) K *
            mode4RootFunction mProject K Λ = 0 := by
      rw [← det_mode4SchurMatrix_eq_upperProd_mul_rootFunction
          mProject K Λ hm (by omega),
        ← det_mode4HermitianSchurMatrix_eq_mode4SchurMatrix_det
          mProject K Λ hm (by omega)]
      exact hdet
    exact (mul_eq_zero.mp hprod).resolve_left
      (ne_of_gt (mode4JacobiUpperProd_pos mProject K hm))
  have hcharacteristic :=
    (mode4DLMF3035EvenCharacteristicEquation_iff_rootFunction_eq_zero
      mProject K Λ hm hK hsep hΛ.le).2 hroot
  exact
    (mode4DLMF3035EvenCharacteristicEquation_iff_leftCoefficient_sqSummable
      mProject K Λ hm hK hsep hΛ.le).1 hcharacteristic

/-- Full production-domain spectral characterization below twenty.  The
existential carrier index is zero-based and source-ordered. -/
theorem
    mode4DLMF3035EvenLeftCoefficient_sqSummable_iff_exists_finiteLimitSpectrum
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ < 20) :
    Summable
        (fun q : ℕ =>
          ‖mode4DLMF3035EvenLeftCoefficient
              (mode4JacobiG mProject) Λ q‖ ^ 2) ↔
      ∃ j : ℕ,
        mode4ClassicalEvenEigenvalue
            (mode4JacobiG mProject) j = Λ := by
  constructor
  · exact
      mode4DLMF3035EvenLeftCoefficient_sqSummable_imp_exists_finiteLimitSpectrum
        mProject K Λ hm hK hsep hΛ
  · rintro ⟨j, hj⟩
    exact
      mode4ClassicalEvenEigenvalue_eq_imp_DLMF3035EvenLeftCoefficient_sqSummable
        mProject K j Λ hm hK hsep hΛ hj

/-- Below the strict endpoint, the zero-based finite-limit carrier index is
exactly the negative-eigenvalue count of the singular literal Schur matrix.
The proof uses both semicontinuity bounds at the simple root and the same
fixed-index finite eigenvalue convergence on the two sides. -/
theorem
    mode4ClassicalEvenEigenvalue_index_eq_literalSchur_negativeCount_of_lt_twenty
    (mProject K j : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ < 20)
    (hcarrier :
      mode4ClassicalEvenEigenvalue
          (mode4JacobiG mProject) j = Λ) :
    mode4HermitianNegativeEigenvalueCount
        (mode4HermitianSchurMatrix mProject Λ K)
        (mode4HermitianSchurMatrix_isHermitian mProject K Λ) = j := by
  let G := mode4JacobiG mProject
  have hG : 0 < G := by
    unfold G mode4JacobiG
    positivity
  have hdetZero :=
    mode4ClassicalEvenEigenvalue_eq_imp_literalSchur_det_eq_zero_of_lt_twenty
      mProject K j Λ hm hK hsep hΛ hcarrier
  have hroot : mode4RootFunction mProject K Λ = 0 := by
    have hprod :
        mode4JacobiUpperProd (mode4JacobiG mProject) K *
            mode4RootFunction mProject K Λ = 0 := by
      rw [← det_mode4SchurMatrix_eq_upperProd_mul_rootFunction
          mProject K Λ hm (by omega),
        ← det_mode4HermitianSchurMatrix_eq_mode4SchurMatrix_det
          mProject K Λ hm (by omega)]
      exact hdetZero
    exact (mul_eq_zero.mp hprod).resolve_left
      (ne_of_gt (mode4JacobiUpperProd_pos mProject K hm))
  let ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hε : Filter.Tendsto ε Filter.atTop (nhds 0) := by
    simpa [ε] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1))
          Filter.atTop (nhds 0))
  have hεpos (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    positivity
  have hloExists :
      ∀ n : ℕ, ∃ x : ℝ,
        Λ - ε n < x ∧ x < Λ ∧
          (mode4HermitianSchurMatrix mProject x K).det ≠ 0 := by
    intro n
    exact exists_mode4HermitianSchurMatrix_det_ne_zero_between
      mProject K (Λ - ε n) Λ hm hK hsep
      (by linarith [hεpos n]) hΛ.le
  let Λlo : ℕ → ℝ := fun n => Classical.choose (hloExists n)
  have hloSpec (n : ℕ) :
      Λ - ε n < Λlo n ∧ Λlo n < Λ ∧
        (mode4HermitianSchurMatrix mProject (Λlo n) K).det ≠ 0 :=
    Classical.choose_spec (hloExists n)
  let b : ℕ → ℝ := fun n => min (Λ + ε n) 20
  have hΛb (n : ℕ) : Λ < b n := by
    dsimp [b]
    exact lt_min (by linarith [hεpos n]) hΛ
  have hhiExists :
      ∀ n : ℕ, ∃ x : ℝ,
        Λ < x ∧ x < b n ∧
          (mode4HermitianSchurMatrix mProject x K).det ≠ 0 := by
    intro n
    exact exists_mode4HermitianSchurMatrix_det_ne_zero_between
      mProject K Λ (b n) hm hK hsep (hΛb n) (min_le_right _ _)
  let Λhi : ℕ → ℝ := fun n => Classical.choose (hhiExists n)
  have hhiSpec (n : ℕ) :
      Λ < Λhi n ∧ Λhi n < b n ∧
        (mode4HermitianSchurMatrix mProject (Λhi n) K).det ≠ 0 :=
    Classical.choose_spec (hhiExists n)
  have hloDist :
      Filter.Tendsto (fun n => dist (Λlo n) Λ) Filter.atTop (nhds 0) := by
    refine squeeze_zero (g := ε) (fun _ => dist_nonneg) (fun n => ?_) hε
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hloSpec n).2.1.le)]
    linarith [(hloSpec n).1]
  have hlo : Filter.Tendsto Λlo Filter.atTop (nhds Λ) := by
    exact (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => Λ) Filter.atTop (nhds Λ)).congr_dist
        (by simpa [dist_comm] using hloDist)
  have hhiDist :
      Filter.Tendsto (fun n => dist (Λhi n) Λ) Filter.atTop (nhds 0) := by
    refine squeeze_zero (g := ε) (fun _ => dist_nonneg) (fun n => ?_) hε
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hhiSpec n).1.le)]
    have hbLe : b n ≤ Λ + ε n := min_le_left _ _
    linarith [(hhiSpec n).2.1]
  have hhi : Filter.Tendsto Λhi Filter.atTop (nhds Λ) := by
    exact (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => Λ) Filter.atTop (nhds Λ)).congr_dist
        (by simpa [dist_comm] using hhiDist)
  have hmatrixContinuous :=
    mode4HermitianSchurMatrix_continuousAt_lambda
      mProject K Λ hm hK hsep hΛ
  have hmatrixLo :
      Filter.Tendsto
        (fun n => mode4HermitianSchurMatrix mProject (Λlo n) K)
        Filter.atTop
        (nhds (mode4HermitianSchurMatrix mProject Λ K)) :=
    hmatrixContinuous.tendsto.comp hlo
  have hmatrixHi :
      Filter.Tendsto
        (fun n => mode4HermitianSchurMatrix mProject (Λhi n) K)
        Filter.atTop
        (nhds (mode4HermitianSchurMatrix mProject Λ K)) :=
    hmatrixContinuous.tendsto.comp hhi
  have hboundsLo :=
    mode4HermitianNegativeEigenvalueCount_eventually_between_of_tendsto
      (fun n => mode4HermitianSchurMatrix mProject (Λlo n) K)
      (fun n => mode4HermitianSchurMatrix_isHermitian mProject K (Λlo n))
      (mode4HermitianSchurMatrix mProject Λ K)
      (mode4HermitianSchurMatrix_isHermitian mProject K Λ)
      hmatrixLo
  have hboundsHi :=
    mode4HermitianNegativeEigenvalueCount_eventually_between_of_tendsto
      (fun n => mode4HermitianSchurMatrix mProject (Λhi n) K)
      (fun n => mode4HermitianSchurMatrix_isHermitian mProject K (Λhi n))
      (mode4HermitianSchurMatrix mProject Λ K)
      (mode4HermitianSchurMatrix_isHermitian mProject K Λ)
      hmatrixHi
  obtain ⟨n, hnLo, hnHi⟩ := (hboundsLo.and hboundsHi).exists
  have hlo20 : Λlo n ≤ 20 :=
    le_trans (hloSpec n).2.1.le hΛ.le
  have hhi20 : Λhi n ≤ 20 :=
    le_trans (hhiSpec n).2.1.le (min_le_right _ _)
  have htransportLo :=
    mode4ActualFiniteJacobiTruncation_negativeCount_eventually_eq_hermitianSchurMatrix
      mProject K (Λlo n) hm hK hsep hlo20 (hloSpec n).2.2
  have htransportHi :=
    mode4ActualFiniteJacobiTruncation_negativeCount_eventually_eq_hermitianSchurMatrix
      mProject K (Λhi n) hm hK hsep hhi20 (hhiSpec n).2.2
  have hfiniteCountLo :
      ∀ᶠ d : ℕ in Filter.atTop,
        (Finset.univ.filter fun p : Fin (K + (j + 1 + d)) =>
          mode4DLMFEvenFiniteEigenvalue G (K + (j + 1 + d)) p <
            Λlo n).card =
        mode4HermitianNegativeEigenvalueCount
          (mode4HermitianSchurMatrix mProject (Λlo n) K)
          (mode4HermitianSchurMatrix_isHermitian mProject K (Λlo n)) := by
    have hpulled := (mode4NatShift_tendsto (j + 1)).eventually htransportLo
    filter_upwards [hpulled] with d hd
    simpa using
      (mode4ActualFiniteJacobiTruncation_negativeCount_eq_finiteCount
        mProject K (j + 1 + d) (Λlo n)).symm.trans hd
  have hfiniteCountHi :
      ∀ᶠ d : ℕ in Filter.atTop,
        (Finset.univ.filter fun p : Fin (K + (j + 1 + d)) =>
          mode4DLMFEvenFiniteEigenvalue G (K + (j + 1 + d)) p <
            Λhi n).card =
        mode4HermitianNegativeEigenvalueCount
          (mode4HermitianSchurMatrix mProject (Λhi n) K)
          (mode4HermitianSchurMatrix_isHermitian mProject K (Λhi n)) := by
    have hpulled := (mode4NatShift_tendsto (j + 1)).eventually htransportHi
    filter_upwards [hpulled] with d hd
    simpa using
      (mode4ActualFiniteJacobiTruncation_negativeCount_eq_finiteCount
        mProject K (j + 1 + d) (Λhi n)).symm.trans hd
  have hconv := mode4CarrierEigenvalue_tendsto_along_schurDepth G K j hG
  have haboveLo :
      ∀ᶠ d : ℕ in Filter.atTop,
        Λlo n <
          mode4DLMFEvenFiniteEigenvalue G (K + (j + 1 + d))
            ⟨j, by omega⟩ :=
    hconv.eventually_const_lt (by rw [hcarrier]; exact (hloSpec n).2.1)
  have hbelowHi :
      ∀ᶠ d : ℕ in Filter.atTop,
        mode4DLMFEvenFiniteEigenvalue G (K + (j + 1 + d))
            ⟨j, by omega⟩ < Λhi n :=
    hconv.eventually_lt_const (by rw [hcarrier]; exact (hhiSpec n).1)
  obtain ⟨d, hdCountLo, hdCountHi, hdAboveLo, hdBelowHi⟩ :=
    (hfiniteCountLo.and
      (hfiniteCountHi.and (haboveLo.and hbelowHi))).exists
  have hcardLo := mode4Card_filter_lt_le_of_monotone'
    (mode4DLMFEvenFiniteEigenvalue G (K + (j + 1 + d)))
    (mode4DLMFEvenFiniteEigenvalue_monotone G (K + (j + 1 + d)))
    (⟨j, by omega⟩ : Fin (K + (j + 1 + d))) (Λlo n) hdAboveLo.le
  have hcardHi := mode4Card_filter_lt_ge_succ_of_monotone'
    (mode4DLMFEvenFiniteEigenvalue G (K + (j + 1 + d)))
    (mode4DLMFEvenFiniteEigenvalue_monotone G (K + (j + 1 + d)))
    (⟨j, by omega⟩ : Fin (K + (j + 1 + d))) (Λhi n) hdBelowHi
  rw [hdCountLo] at hcardLo
  rw [hdCountHi] at hcardHi
  have hnullity :
      Module.finrank ℝ
        (LinearMap.ker
          (mode4HermitianSchurMatrix mProject Λ K).mulVecLin) = 1 := by
    exact mode4HermitianSchurMatrix_root_ker_finrank_eq_one
      mProject K Λ hm (by omega) hroot
  let r :=
    mode4HermitianNegativeEigenvalueCount
      (mode4HermitianSchurMatrix mProject Λ K)
      (mode4HermitianSchurMatrix_isHermitian mProject K Λ)
  let rlo :=
    mode4HermitianNegativeEigenvalueCount
      (mode4HermitianSchurMatrix mProject (Λlo n) K)
      (mode4HermitianSchurMatrix_isHermitian mProject K (Λlo n))
  let rhi :=
    mode4HermitianNegativeEigenvalueCount
      (mode4HermitianSchurMatrix mProject (Λhi n) K)
      (mode4HermitianSchurMatrix_isHermitian mProject K (Λhi n))
  have hrLeLo : r ≤ rlo := by
    simpa [r, rlo] using hnLo.1
  have hloLeJ : rlo ≤ j := by
    simpa [rlo] using hcardLo
  have hjLeHi : j + 1 ≤ rhi := by
    simpa [rhi] using hcardHi
  have hhiLe : rhi ≤ r + 1 := by
    have h := hnHi.2
    rw [hnullity] at h
    simpa [r, rhi] using h
  omega

/-- On every production window below twenty, the zero-based finite-limit even
carrier is strictly ordered.  This is the no-collision theorem needed before
selecting the degree-four index `2`. -/
theorem mode4ClassicalEvenEigenvalue_lt_of_index_lt_of_upper_lt_twenty
    (mProject K j k : ℕ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hjk : j < k)
    (hk20 :
      mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) k < 20) :
    mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) j <
      mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) k := by
  have hG : 0 < mode4JacobiG mProject := by
    unfold mode4JacobiG
    positivity
  have hle :=
    mode4ClassicalEvenEigenvalue_monotone
      (mode4JacobiG mProject) hG hjk.le
  apply lt_of_le_of_ne hle
  intro heq
  have hjLabel :=
    mode4ClassicalEvenEigenvalue_index_eq_literalSchur_negativeCount_of_lt_twenty
      mProject K j
      (mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) k)
      hm hK hsep hk20 heq
  have hkLabel :=
    mode4ClassicalEvenEigenvalue_index_eq_literalSchur_negativeCount_of_lt_twenty
      mProject K k
      (mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) k)
      hm hK hsep hk20 rfl
  exact hjk.ne (hjLabel.symm.trans hkLabel)

/-- The third zero-based even carrier is the unique carrier index with its
value.  In DLMF's parity-compressed enumeration this is the degree-four mode
`2p = 4`. -/
theorem mode4ClassicalEvenEigenvalue_eq_two_iff_index_eq_two
    (mProject K j : ℕ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20) :
    mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) j =
        mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 2 ↔
      j = 2 := by
  constructor
  · intro hj
    have hG : 0 < mode4JacobiG mProject := by
      unfold mode4JacobiG
      positivity
    have htwo20 :=
      mode4ClassicalEvenEigenvalue_two_lt_twenty
        (mode4JacobiG mProject) hG
    have hjLabel :=
      mode4ClassicalEvenEigenvalue_index_eq_literalSchur_negativeCount_of_lt_twenty
        mProject K j
        (mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 2)
        hm hK hsep htwo20 hj
    have htwoLabel :=
      mode4ClassicalEvenEigenvalue_index_eq_literalSchur_negativeCount_of_lt_twenty
        mProject K 2
        (mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 2)
        hm hK hsep htwo20 rfl
    exact hjLabel.symm.trans htwoLabel
  · rintro rfl
    rfl

/-- The normalized DLMF 30.3.5 even coefficient row at the unique degree-four
carrier is square-summable.  This is the exact spectral mode-selection output;
it is not yet the physical PSWF or finite-Fourier eigenrelation. -/
theorem mode4DLMF3035EvenLeftCoefficient_degreeFour_sqSummable
    (mProject K : ℕ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20) :
    Summable
      (fun q : ℕ =>
        ‖mode4DLMF3035EvenLeftCoefficient
            (mode4JacobiG mProject)
            (mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 2) q‖ ^ 2) := by
  have hG : 0 < mode4JacobiG mProject := by
    unfold mode4JacobiG
    positivity
  exact
    mode4ClassicalEvenEigenvalue_eq_imp_DLMF3035EvenLeftCoefficient_sqSummable
      mProject K 2
      (mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 2)
      hm hK hsep
      (mode4ClassicalEvenEigenvalue_two_lt_twenty
        (mode4JacobiG mProject) hG)
      rfl

#print axioms
  mode4ClassicalEvenEigenvalue_eq_imp_literalSchur_det_eq_zero_of_lt_twenty
#print axioms
  mode4ClassicalEvenEigenvalue_eq_imp_DLMF3035EvenLeftCoefficient_sqSummable
#print axioms
  mode4DLMF3035EvenLeftCoefficient_sqSummable_iff_exists_finiteLimitSpectrum
#print axioms
  mode4ClassicalEvenEigenvalue_index_eq_literalSchur_negativeCount_of_lt_twenty
#print axioms
  mode4ClassicalEvenEigenvalue_lt_of_index_lt_of_upper_lt_twenty
#print axioms mode4ClassicalEvenEigenvalue_eq_two_iff_index_eq_two
#print axioms mode4DLMF3035EvenLeftCoefficient_degreeFour_sqSummable

end

end Q3.RouteB
