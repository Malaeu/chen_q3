import Q3.Proofs.RouteB.D0CanonicalApproximation
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace Q3.RouteB.D0Pstar

/-- D0.1 source lock:
`ACTIVE/requests/routeB_lamport_rh_closure/D0_1_EXACT_HILBERT_SPACE_AND_NORM.md:27`
and `literature/zotero/H8ULBMAL/fulltext.md:285`.
-/
def lambda_m (i : PairIndex) : ℝ :=
  Real.sqrt i.m

/-- D0.1 source lock:
`ACTIVE/requests/routeB_lamport_rh_closure/D0_1_EXACT_HILBERT_SPACE_AND_NORM.md:28`
and `literature/zotero/H8ULBMAL/fulltext.md:285`.
-/
abbrev L_m (i : PairIndex) : ℝ :=
  logLength i

/-- D0.1 source lock:
`ACTIVE/requests/routeB_lamport_rh_closure/D0_1_EXACT_HILBERT_SPACE_AND_NORM.md:37`
and `literature/zotero/H8ULBMAL/fulltext.md:312-313`.
-/
def dStar : Measure ℝ :=
  volume.withDensity (fun u : ℝ => ENNReal.ofReal u⁻¹)

/-- D0.1 multiplicative window, source-locked at
`ACTIVE/requests/routeB_lamport_rh_closure/D0_1_EXACT_HILBERT_SPACE_AND_NORM.md:37`
and `literature/zotero/H8ULBMAL/fulltext.md:285-286`.
-/
def I_m (i : PairIndex) : Set ℝ :=
  Set.Icc (lambda_m i)⁻¹ (lambda_m i)

/-- Exact D0.1 carrier
`H_m = L²([lambda_m⁻¹,lambda_m], du/u)`.

Source lock:
`ACTIVE/requests/routeB_lamport_rh_closure/D0_1_EXACT_HILBERT_SPACE_AND_NORM.md:34-38`;
`literature/zotero/H8ULBMAL/fulltext.md:285-288,312-313`.
-/
abbrev H_m (i : PairIndex) :=
  MeasureTheory.Lp ℂ 2 (dStar.restrict (I_m i))

/-- The pointwise D0.1 mode `V_(n,m)=kappa_m(U_(n,m))`, with the definitions
of `kappa_m` and `U_(n,m)` unfolded.

Source lock:
`ACTIVE/requests/routeB_lamport_rh_closure/D0_1_EXACT_HILBERT_SPACE_AND_NORM.md:43-51`;
`literature/zotero/H8ULBMAL/fulltext.md:108-112,285-290,333-335`.
-/
def V_n_m (i : PairIndex) (n : ℤ) : H_m i :=
  MemLp.toLp
    (fun u : ℝ =>
      ((Real.sqrt (L_m i))⁻¹ : ℂ) *
        Complex.exp
          (2 * Real.pi * Complex.I * n *
            (Real.log (lambda_m i * u) / L_m i)))
    (by
      have hm_real : (1 : ℝ) < i.m := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) i.hm)
      have hlambda : 1 < lambda_m i := by
        simpa [lambda_m] using
          (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hm_real :
            Real.sqrt 1 < Real.sqrt i.m)
      have hinv :
          IntegrableOn (fun u : ℝ => u⁻¹) (I_m i) volume := by
        apply ContinuousOn.integrableOn_Icc
        apply continuousOn_id.inv₀
        intro u hu
        apply ne_of_gt
        exact (inv_pos.mpr (zero_lt_one.trans hlambda)).trans_le hu.1
      letI : IsFiniteMeasure (dStar.restrict (I_m i)) :=
        ⟨by
          rw [Measure.restrict_apply_univ, dStar, I_m,
            withDensity_apply _ measurableSet_Icc]
          simpa [I_m] using hinv.setLIntegral_lt_top⟩
      have hlog :
          ContinuousOn
            (fun u : ℝ => Real.log (lambda_m i * u)) (I_m i) := by
        apply (continuousOn_const.mul continuousOn_id).log
        intro u hu
        apply ne_of_gt
        exact mul_pos (zero_lt_one.trans hlambda)
          ((inv_pos.mpr (zero_lt_one.trans hlambda)).trans_le hu.1)
      have hcomplexlog :
          ContinuousOn
            (fun u : ℝ => (Real.log (lambda_m i * u) : ℂ)) (I_m i) :=
        Complex.continuous_ofReal.comp_continuousOn hlog
      have hexponent :
          ContinuousOn
            (fun u : ℝ =>
              2 * Real.pi * Complex.I * n *
                (Real.log (lambda_m i * u) / L_m i)) (I_m i) := by
        fun_prop
      have hmode :
          ContinuousOn
            (fun u : ℝ =>
              ((Real.sqrt (L_m i))⁻¹ : ℂ) *
                Complex.exp
                  (2 * Real.pi * Complex.I * n *
                    (Real.log (lambda_m i * u) / L_m i))) (I_m i) :=
        continuousOn_const.mul hexponent.cexp
      refine MemLp.of_bound
        (hmode.aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc)
        ‖((Real.sqrt (L_m i))⁻¹ : ℂ)‖ ?_
      · filter_upwards [] with u
        rw [norm_mul, Complex.norm_exp]
        simp)

/-- Exact D0.1 Galerkin carrier
`E_(m,N)=span_C {V_(n,m) : -N <= n <= N}`.

Source lock:
`ACTIVE/requests/routeB_lamport_rh_closure/D0_1_EXACT_HILBERT_SPACE_AND_NORM.md:54-59`;
`literature/zotero/H8ULBMAL/fulltext.md:333-339,702-704,734-735`.
-/
def E_m_N (i : PairIndex) : Submodule ℂ (H_m i) :=
  Submodule.span ℂ (V_n_m i '' (modeSet i : Set ℤ))

/-- Exact D0.1 orthogonal projection `P_(m,N) : H_m -> E_(m,N)`.

Source lock:
`ACTIVE/requests/routeB_lamport_rh_closure/D0_1_EXACT_HILBERT_SPACE_AND_NORM.md:61`;
`literature/zotero/H8ULBMAL/fulltext.md:702-704,734-735`.
-/
def P_m_N (i : PairIndex) : H_m i →L[ℂ] E_m_N i :=
  letI : FiniteDimensional ℂ (E_m_N i) :=
    FiniteDimensional.span_of_finite ℂ
      ((modeSet i).finite_toSet.image (V_n_m i))
  letI : CompleteSpace (E_m_N i) :=
    FiniteDimensional.complete ℂ (E_m_N i)
  (E_m_N i).orthogonalProjection

#print axioms lambda_m
#print axioms L_m
#print axioms dStar
#print axioms I_m
#print axioms H_m
#print axioms V_n_m
#print axioms E_m_N
#print axioms P_m_N

end Q3.RouteB.D0Pstar
