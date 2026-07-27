import Q3.Proofs.RouteB.D0CenteredCriticalMoment

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace Q3.RouteB.D0Pstar

/-- The zero Fourier mode belongs to the exact Galerkin carrier.  This is the
missing named form of the second source-lock check in goal 006. -/
theorem V0_mem_E_m_N (i : PairIndex) :
    V_n_m i 0 ∈ E_m_N i := by
  apply Submodule.subset_span
  exact ⟨0, by simp [modeSet], rfl⟩

/-- Orthogonal projection preserves the `V₀` overlap. -/
theorem inner_V0_gTrial_m_N_eq
    (i : PairIndex)
    (hTrial_m : ℝ → ℂ)
    (hE_star :
      MemLp (E_star hTrial_m) 2 (dStar.restrict (I_m i))) :
    inner ℂ (V_n_m i 0)
        (gTrial_m_N i hTrial_m hE_star : H_m i) =
      inner ℂ (V_n_m i 0) (gTrial_m i hTrial_m hE_star) := by
  letI : FiniteDimensional ℂ (E_m_N i) :=
    FiniteDimensional.span_of_finite ℂ
      ((modeSet i).finite_toSet.image (V_n_m i))
  letI : CompleteSpace (E_m_N i) :=
    FiniteDimensional.complete ℂ (E_m_N i)
  let v0 : E_m_N i := ⟨V_n_m i 0, V0_mem_E_m_N i⟩
  change inner ℂ v0
      ((E_m_N i).orthogonalProjection
        (gTrial_m i hTrial_m hE_star)) =
    inner ℂ (v0 : H_m i) (gTrial_m i hTrial_m hE_star)
  exact (E_m_N i).inner_orthogonalProjection_eq_of_mem_left
    v0 (gTrial_m i hTrial_m hE_star)

/-- The exact Galerkin projection is norm non-increasing in the same `H_m`
norm used by `sTrial_m_N`. -/
theorem norm_gTrial_m_N_le
    (i : PairIndex)
    (hTrial_m : ℝ → ℂ)
    (hE_star :
      MemLp (E_star hTrial_m) 2 (dStar.restrict (I_m i))) :
    ‖gTrial_m_N i hTrial_m hE_star‖ ≤
      ‖gTrial_m i hTrial_m hE_star‖ := by
  letI : FiniteDimensional ℂ (E_m_N i) :=
    FiniteDimensional.span_of_finite ℂ
      ((modeSet i).finite_toSet.image (V_n_m i))
  letI : CompleteSpace (E_m_N i) :=
    FiniteDimensional.complete ℂ (E_m_N i)
  simpa [gTrial_m_N, P_m_N] using
    (E_m_N i).norm_orthogonalProjection_apply_le
      (gTrial_m i hTrial_m hE_star)

/-- Positive unprojected central mass forces the projected trial to be
nonzero; no lower bound on the projected norm is used. -/
theorem gTrial_m_N_ne_zero_of_unprojected_central_mass
    (i : PairIndex)
    (hTrial_m : ℝ → ℂ)
    (hE_star :
      MemLp (E_star hTrial_m) 2 (dStar.restrict (I_m i)))
    (a : ℝ) (ha : 0 < a)
    (hmass :
      a ≤ Real.sqrt (L_m i) *
        ‖inner ℂ (V_n_m i 0) (gTrial_m i hTrial_m hE_star)‖) :
    gTrial_m_N i hTrial_m hE_star ≠ 0 := by
  intro hzero
  have hoverlap_zero :
      inner ℂ (V_n_m i 0) (gTrial_m i hTrial_m hE_star) = 0 := by
    rw [← inner_V0_gTrial_m_N_eq i hTrial_m hE_star, hzero]
    simp
  rw [hoverlap_zero, norm_zero, mul_zero] at hmass
  exact (not_lt_of_ge hmass) ha

/-- `D0AnchorFloorFromUnprojectedCentralMass`.

The theorem packet follows the six-line route in goal 006.  The output
contains projected nonvanishing, an inhabitant of the central-index locus,
the coefficient floor, and the raw-transform anchor floor.  `hbind` is the
exact Stage-3 bind of the abstract `CoefficientFamily` row to the constructed
normalized projection; it introduces no scalar or phase. -/
theorem D0AnchorFloorFromUnprojectedCentralMass
    (D : CoefficientFamily)
    (i : PairIndex)
    (hTrial_m : ℝ → ℂ)
    (hE_star :
      MemLp (E_star hTrial_m) 2 (dStar.restrict (I_m i)))
    (hbind :
      ∀ hTrialNonzero : TrialNonzero i hTrial_m hE_star,
        ∀ n : ℤ,
          D.kTrial i n =
            c_n i hTrial_m hE_star hTrialNonzero n)
    (a C : ℝ) (ha : 0 < a) (hC : 0 < C)
    (hmass :
      a ≤ Real.sqrt (L_m i) *
        ‖inner ℂ (V_n_m i 0) (gTrial_m i hTrial_m hE_star)‖)
    (hbound : ‖gTrial_m i hTrial_m hE_star‖ ≤ C) :
    gTrial_m_N i hTrial_m hE_star ≠ 0 ∧
      (∃ ci : CentralIndex D, ci.1 = i) ∧
      a / C ≤ Real.sqrt (L_m i) * ‖D.kTrial i 0‖ ∧
      a / C ≤ ‖rawFplus D i 0‖ := by
  have hprojected_ne :
      gTrial_m_N i hTrial_m hE_star ≠ 0 :=
    gTrial_m_N_ne_zero_of_unprojected_central_mass
      i hTrial_m hE_star a ha hmass
  have hTrialNonzero : TrialNonzero i hTrial_m hE_star := by
    exact norm_pos_iff.mpr hprojected_ne
  have hprojected_pos :
      0 < ‖gTrial_m_N i hTrial_m hE_star‖ :=
    hTrialNonzero
  have hprojected_le_C :
      ‖gTrial_m_N i hTrial_m hE_star‖ ≤ C :=
    (norm_gTrial_m_N_le i hTrial_m hE_star).trans hbound
  have hc0 :
      ‖D.kTrial i 0‖ =
        ‖inner ℂ (V_n_m i 0) (gTrial_m i hTrial_m hE_star)‖ /
          ‖gTrial_m_N i hTrial_m hE_star‖ := by
    rw [hbind hTrialNonzero 0]
    unfold c_n kTrial_m_N sTrial_m_N
    rw [Submodule.coe_smul, inner_smul_right, norm_mul]
    rw [inner_V0_gTrial_m_N_eq i hTrial_m hE_star]
    simp [div_eq_inv_mul, norm_inv]
  have hnumerator_nonneg :
      0 ≤ Real.sqrt (L_m i) *
        ‖inner ℂ (V_n_m i 0) (gTrial_m i hTrial_m hE_star)‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hcoefficient_floor :
      a / C ≤ Real.sqrt (L_m i) * ‖D.kTrial i 0‖ := by
    calc
      a / C ≤
          (Real.sqrt (L_m i) *
            ‖inner ℂ (V_n_m i 0) (gTrial_m i hTrial_m hE_star)‖) / C :=
        (div_le_div_iff_of_pos_right hC).2 hmass
      _ ≤
          (Real.sqrt (L_m i) *
            ‖inner ℂ (V_n_m i 0) (gTrial_m i hTrial_m hE_star)‖) /
              ‖gTrial_m_N i hTrial_m hE_star‖ :=
        div_le_div_of_nonneg_left
          hnumerator_nonneg hprojected_pos hprojected_le_C
      _ = Real.sqrt (L_m i) * ‖D.kTrial i 0‖ := by
        rw [hc0]
        ring
  have hraw_norm :
      ‖rawFplus D i 0‖ =
        Real.sqrt (L_m i) * ‖D.kTrial i 0‖ := by
    rw [rawFplus_zero_eq_sqrt_mul_c0]
    simp [Real.sqrt_nonneg]
  have hanchor_floor : a / C ≤ ‖rawFplus D i 0‖ := by
    rw [hraw_norm]
    exact hcoefficient_floor
  have hraw_ne : rawFplus D i 0 ≠ 0 := by
    apply norm_pos_iff.mp
    exact (div_pos ha hC).trans_le hanchor_floor
  have hbare_ne : bareTransform D i 0 ≠ 0 := by
    simpa [bareTransform] using hraw_ne
  let ci : CentralIndex D := ⟨i, hbare_ne⟩
  exact ⟨hprojected_ne, ⟨ci, rfl⟩,
    hcoefficient_floor, hanchor_floor⟩

/-- The scale-invariant anchor receiver.  A single positive relative central
mass bound supplies both source constants required by
`D0AnchorFloorFromUnprojectedCentralMass`. -/
theorem D0AnchorFloorFromUnprojectedMassNormRatio
    (D : CoefficientFamily)
    (i : PairIndex)
    (hTrial_m : ℝ → ℂ)
    (hE_star :
      MemLp (E_star hTrial_m) 2 (dStar.restrict (I_m i)))
    (hbind :
      ∀ hTrialNonzero : TrialNonzero i hTrial_m hE_star,
        ∀ n : ℤ,
          D.kTrial i n =
            c_n i hTrial_m hE_star hTrialNonzero n)
    (δ : ℝ)
    (hδ : 0 < δ)
    (hmass_pos :
      0 <
        Real.sqrt (L_m i) *
          ‖inner ℂ (V_n_m i 0)
            (gTrial_m i hTrial_m hE_star)‖)
    (hratio :
      δ * ‖gTrial_m i hTrial_m hE_star‖ ≤
        Real.sqrt (L_m i) *
          ‖inner ℂ (V_n_m i 0)
            (gTrial_m i hTrial_m hE_star)‖) :
    gTrial_m_N i hTrial_m hE_star ≠ 0 ∧
      (∃ ci : CentralIndex D, ci.1 = i) ∧
      δ ≤ Real.sqrt (L_m i) * ‖D.kTrial i 0‖ ∧
      δ ≤ ‖rawFplus D i 0‖ := by
  have hg_ne : gTrial_m i hTrial_m hE_star ≠ 0 := by
    intro hg_zero
    rw [hg_zero, inner_zero_right, norm_zero, mul_zero] at hmass_pos
    exact (lt_irrefl 0) hmass_pos
  have hg_norm_pos : 0 < ‖gTrial_m i hTrial_m hE_star‖ :=
    norm_pos_iff.mpr hg_ne
  have hpacket :=
    D0AnchorFloorFromUnprojectedCentralMass
      D i hTrial_m hE_star hbind
      (δ * ‖gTrial_m i hTrial_m hE_star‖)
      ‖gTrial_m i hTrial_m hE_star‖
      (mul_pos hδ hg_norm_pos) hg_norm_pos hratio le_rfl
  simpa [hg_norm_pos.ne'] using hpacket

#print axioms V0_mem_E_m_N
#print axioms inner_V0_gTrial_m_N_eq
#print axioms norm_gTrial_m_N_le
#print axioms gTrial_m_N_ne_zero_of_unprojected_central_mass
#print axioms D0AnchorFloorFromUnprojectedCentralMass
#print axioms D0AnchorFloorFromUnprojectedMassNormRatio

end Q3.RouteB.D0Pstar
