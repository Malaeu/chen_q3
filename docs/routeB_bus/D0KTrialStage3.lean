import Q3.Proofs.RouteB.D0KTrialStage2

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace Q3.RouteB.D0Pstar

/-- The exact D0.5 nonzero locus for the projected trial.

Source lock:
`ACTIVE/requests/routeB_lamport_rh_closure/D0_5_GROUND_AND_TRIAL_TYPES.md:94-103`;
`ACTIVE/requests/routeB_lamport_rh_closure/D0_7_EXACT_NORMALIZATION_REGISTRY.md:96-107`.
-/
def TrialNonzero
    (i : PairIndex)
    (hTrial_m : ℝ → ℂ)
    (hE_star :
      MemLp (E_star hTrial_m) 2 (dStar.restrict (I_m i))) : Prop :=
  0 < ‖gTrial_m_N i hTrial_m hE_star‖

/-- The positive D0.7b trial normalizer
`sTrial_(m,N)=||gTrial_(m,N)||⁻¹`, defined only with a certificate that the
projected trial is nonzero.

Source lock:
`ACTIVE/requests/routeB_lamport_rh_closure/D0_7_EXACT_NORMALIZATION_REGISTRY.md:96-107`;
`docs/PEN_3_3_G04_OBJECT_DICTIONARY.md:195-215`.
-/
def sTrial_m_N
    (i : PairIndex)
    (hTrial_m : ℝ → ℂ)
    (hE_star :
      MemLp (E_star hTrial_m) 2 (dStar.restrict (I_m i)))
    (_hTrialNonzero : TrialNonzero i hTrial_m hE_star) : ℝ :=
  ‖gTrial_m_N i hTrial_m hE_star‖⁻¹

/-- The exact normalized finite D0 trial
`kTrial_(m,N)=sTrial_(m,N) gTrial_(m,N)` on `TrialNonzero`.

Source lock:
`ACTIVE/requests/routeB_lamport_rh_closure/D0_5_GROUND_AND_TRIAL_TYPES.md:94-105`;
`ACTIVE/requests/routeB_lamport_rh_closure/D0_7_EXACT_NORMALIZATION_REGISTRY.md:96-107`;
`docs/PEN_3_3_G04_OBJECT_DICTIONARY.md:195-215`.
-/
def kTrial_m_N
    (i : PairIndex)
    (hTrial_m : ℝ → ℂ)
    (hE_star :
      MemLp (E_star hTrial_m) 2 (dStar.restrict (I_m i)))
    (hTrialNonzero : TrialNonzero i hTrial_m hE_star) :
    E_m_N i :=
  ((sTrial_m_N i hTrial_m hE_star hTrialNonzero : ℝ) : ℂ) •
    gTrial_m_N i hTrial_m hE_star

/-- D0.7b's exact unit normalization. -/
theorem norm_kTrial_m_N
    (i : PairIndex)
    (hTrial_m : ℝ → ℂ)
    (hE_star :
      MemLp (E_star hTrial_m) 2 (dStar.restrict (I_m i)))
    (hTrialNonzero : TrialNonzero i hTrial_m hE_star) :
    ‖kTrial_m_N i hTrial_m hE_star hTrialNonzero‖ = 1 := by
  have hg_pos : 0 < ‖gTrial_m_N i hTrial_m hE_star‖ :=
    hTrialNonzero
  simp only [kTrial_m_N, norm_smul, sTrial_m_N, norm_real,
    Real.norm_eq_abs, abs_inv, abs_norm]
  exact inv_mul_cancel₀ (ne_of_gt hg_pos)

/-- The source coefficient convention
`c_n(kTrial_(m,N))=<V_(n,m),kTrial_(m,N)>`.

Source lock:
`ACTIVE/requests/routeB_lamport_rh_closure/D0_7E_OWNER_INPUT.md:32-38`;
`ACTIVE/requests/routeB_lamport_rh_closure/D0_7E_CENTRAL_MELLIN_CALIBRATION.md:129-143`;
`ACTIVE/requests/routeB_lamport_rh_closure/D0_6_EXACT_TRANSFORM_CONVENTION.md:105-117`.
-/
def c_n
    (i : PairIndex)
    (hTrial_m : ℝ → ℂ)
    (hE_star :
      MemLp (E_star hTrial_m) 2 (dStar.restrict (I_m i)))
    (hTrialNonzero : TrialNonzero i hTrial_m hE_star)
    (n : ℤ) : ℂ :=
  inner ℂ (V_n_m i n)
    (kTrial_m_N i hTrial_m hE_star hTrialNonzero : H_m i)

/-- The requested bind into `D0CanonicalApproximation`: the existing
`CoefficientFamily.kTrial` field reduces to the coefficient formula of the
constructed normalized projected trial.  This introduces no new object name
outside the D0 glossary. -/
example
    (hTrial_m : (i : PairIndex) → ℝ → ℂ)
    (hE_star :
      ∀ i, MemLp (E_star (hTrial_m i)) 2 (dStar.restrict (I_m i)))
    (hTrialNonzero :
      ∀ i, TrialNonzero i (hTrial_m i) (hE_star i))
    (i : PairIndex) (n : ℤ) :
    (show CoefficientFamily from
      ⟨fun i n =>
        c_n i (hTrial_m i) (hE_star i) (hTrialNonzero i) n⟩).kTrial i n =
      c_n i (hTrial_m i) (hE_star i) (hTrialNonzero i) n :=
  rfl

#print axioms TrialNonzero
#print axioms sTrial_m_N
#print axioms kTrial_m_N
#print axioms norm_kTrial_m_N
#print axioms c_n

end Q3.RouteB.D0Pstar
