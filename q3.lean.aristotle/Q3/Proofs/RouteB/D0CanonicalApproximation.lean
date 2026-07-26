import Q3.Proofs.RouteB.CanonicalRHRouteSkeleton
import Q3.Proofs.RouteB.RawIntegralRhsCrosswalk

set_option linter.mathlibStandardSet false

open Filter
open scoped Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

open CanonicalRHRoute

/-- The independent D0 parameters.  The lower bound `m ≥ 2` ensures that the
logarithmic window has positive length. -/
structure PairIndex where
  m : ℕ
  N : ℕ
  hm : 2 ≤ m

/-- The D0 logarithmic window length `L_m = log m`. -/
def logLength (i : PairIndex) : ℝ :=
  Real.log i.m

/-- The D0 Galerkin sector `{-N, ..., N}`. -/
def modeSet (i : PairIndex) : Finset ℤ :=
  Finset.Icc (-(i.N : ℤ)) (i.N : ℤ)

/-- The D0 `kTrial_(m,N)` coefficient row used by the finite transform.
Stage 3 of the kTrial realization supplies this field from the normalized
projected vector, rather than leaving an unrelated free `coeff` selector.
This record still does not assert that an arbitrary row is a ground family. -/
structure CoefficientFamily where
  kTrial : PairIndex → ℤ → ℂ

/-- The raw D0 family
`Fplus_(m,N)(z) = T_m(k_(m,N))(-z)`, in removable Proposition-5.9 form. -/
def rawFplus (D : CoefficientFamily) (i : PairIndex) (z : ℂ) : ℂ :=
  proposition59RawTransform (logLength i) (modeSet i) (D.kTrial i) (-z)

/-- The SOFT-1 bare transform
`B_(m,N)(z) = lambda_m^(i*z) Fplus_(m,N)(z)`.
Since `L_m = 2 log lambda_m`, the multiplier is `exp(i*z*L_m/2)`. -/
def bareTransform (D : CoefficientFamily) (i : PairIndex) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * z * (logLength i : ℂ) / 2) * rawFplus D i z

/-- The exact central-nonzero locus needed for normalization.  It is not
silently inferred from `TrialNonzero`. -/
def CentralIndex (D : CoefficientFamily) :=
  {i : PairIndex // bareTransform D i 0 ≠ 0}

/-- Legacy uncentered candidate.  The 2026-07-27 S1 verdict kills this family:
its factor `exp(i*z*L_m/2)` forces polynomial growth in `m` even inside the
centered critical strip.  It is retained only as a no-go witness. -/
def pstarFamily
    (D : CoefficientFamily) (i : CentralIndex D) (z : ℂ) : ℂ :=
  (centeredXi 0 / bareTransform D i.1 0) * bareTransform D i.1 z

/-- The centered canonical D0 family, verbatim from section iii of
`PROSHKA_VERDICT_S1_ANCHOR_2026-07-27.md`. -/
def centeredPstarFamily
    (D : CoefficientFamily) (i : CentralIndex D) (z : ℂ) : ℂ :=
  (centeredXi 0 / rawFplus D i.1 0) * rawFplus D i.1 z

/-- Cofinality means that both independent D0 coordinates tend to infinity. -/
def PairCofinal {D : CoefficientFamily} (p : ℕ → CentralIndex D) : Prop :=
  Tendsto (fun k => (p k).1.m) atTop atTop ∧
    Tendsto (fun k => (p k).1.N) atTop atTop

/-- Data not yet supplied by D0: the exact coefficient selector, a cofinal
path in the central-nonzero locus, and the one nested extraction. -/
structure CanonicalData where
  kTrial : CoefficientFamily
  parent : ℕ → CentralIndex kTrial
  parentCofinal : PairCofinal parent
  extract : ℕ → ℕ
  extractStrictMono : StrictMono extract

/-- Hole-free structural realization of `CanonicalApproximation` for the raw,
central-normalized D0 family. -/
def canonicalApproximation (D : CanonicalData) :
    CanonicalApproximation (CentralIndex D.kTrial) where
  Pstar := ⟨centeredPstarFamily D.kTrial⟩
  parent := D.parent
  parentCofinal := PairCofinal D.parent
  parentCofinalProof := D.parentCofinal
  extract := D.extract
  extractStrictMono := D.extractStrictMono

theorem logLength_pos (i : PairIndex) :
    0 < logLength i := by
  unfold logLength
  apply Real.log_pos
  exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) i.hm)

theorem rawFplus_eq_D0_integral
    (D : CoefficientFamily) (i : PairIndex) (z : ℂ) :
    finiteFplusCenteredIntegral
        (logLength i) (modeSet i) (D.kTrial i) z =
      rawFplus D i z := by
  rw [finiteFplusCenteredIntegral_eq_proposition59RawTransform_neg
    (logLength_pos i).ne']
  rfl

theorem differentiable_rawFplus
    (D : CoefficientFamily) (i : PairIndex) :
    Differentiable ℂ (rawFplus D i) := by
  have hneg : Differentiable ℂ (fun z : ℂ => -z) := by fun_prop
  simpa [rawFplus, Function.comp_def] using
    (differentiable_proposition59RawTransform
      (logLength i) (modeSet i) (D.kTrial i)).comp hneg

theorem differentiable_bareTransform
    (D : CoefficientFamily) (i : PairIndex) :
    Differentiable ℂ (bareTransform D i) := by
  have hphase :
      Differentiable ℂ
        (fun z : ℂ => Complex.exp (Complex.I * z * (logLength i : ℂ) / 2)) := by
    fun_prop
  exact hphase.mul (differentiable_rawFplus D i)

@[simp] theorem pstarFamily_zero
    (D : CoefficientFamily) (i : CentralIndex D) :
    pstarFamily D i 0 = centeredXi 0 := by
  unfold pstarFamily
  field_simp [i.property]

theorem differentiable_pstarFamily
    (D : CoefficientFamily) (i : CentralIndex D) :
    Differentiable ℂ (pstarFamily D i) := by
  have hbare := differentiable_bareTransform D i.1
  have hscaled :
      Differentiable ℂ
        (fun z =>
          (centeredXi 0 / bareTransform D i.1 0) * bareTransform D i.1 z) :=
    hbare.const_mul _
  exact hscaled

/-- The central locus defined through `bareTransform` is exactly sufficient
for the centered denominator because the phase equals one at zero. -/
theorem rawFplus_zero_ne
    (D : CoefficientFamily) (i : CentralIndex D) :
    rawFplus D i.1 0 ≠ 0 := by
  simpa [bareTransform] using i.property

@[simp] theorem centeredPstarFamily_zero
    (D : CoefficientFamily) (i : CentralIndex D) :
    centeredPstarFamily D i 0 = centeredXi 0 := by
  unfold centeredPstarFamily
  field_simp [rawFplus_zero_ne D i]

theorem differentiable_centeredPstarFamily
    (D : CoefficientFamily) (i : CentralIndex D) :
    Differentiable ℂ (centeredPstarFamily D i) := by
  exact (differentiable_rawFplus D i.1).const_mul _

/-- Under the classical nonvanishing of `Xi(0)`, the centered canonical
family has exactly the zeros of the raw transform. -/
theorem centeredPstarFamily_eq_zero_iff
    (D : CoefficientFamily) (i : CentralIndex D)
    (hXi : centeredXi 0 ≠ 0) (z : ℂ) :
    centeredPstarFamily D i z = 0 ↔ rawFplus D i.1 z = 0 := by
  simp [centeredPstarFamily, div_eq_mul_inv, hXi, rawFplus_zero_ne D i]

/-- Legacy zero-set statement for the killed uncentered witness. -/
theorem pstarFamily_eq_zero_iff
    (D : CoefficientFamily) (i : CentralIndex D)
    (hXi : centeredXi 0 ≠ 0) (z : ℂ) :
    pstarFamily D i z = 0 ↔ rawFplus D i.1 z = 0 := by
  have hraw0 : rawFplus D i.1 0 ≠ 0 := by
    intro h
    apply i.property
    simp [bareTransform, h]
  simp [pstarFamily, bareTransform, div_eq_mul_inv, hXi, hraw0]

theorem canonicalApproximation_slotH1 (D : CanonicalData) :
    SlotH1 (canonicalApproximation D) := by
  intro i
  exact differentiable_centeredPstarFamily D.kTrial i

theorem canonicalApproximation_slotAnchor (D : CanonicalData) :
    SlotAnchor (canonicalApproximation D) 0 := by
  intro i
  exact centeredPstarFamily_zero D.kTrial i

#print axioms rawFplus_eq_D0_integral
#print axioms centeredPstarFamily_eq_zero_iff
#print axioms pstarFamily_eq_zero_iff
#print axioms canonicalApproximation_slotH1
#print axioms canonicalApproximation_slotAnchor

end Q3.RouteB.D0Pstar
