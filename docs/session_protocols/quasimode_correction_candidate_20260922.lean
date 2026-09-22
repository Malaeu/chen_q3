import Mathlib
open Polynomial
noncomputable section
namespace Q3QuasimodeCorrection
abbrev P0 : ℝ[X] := 1
abbrev P4 : ℝ[X] := 3 - 24*X^2 + 16*X^4
abbrev Q0 : ℝ[X] := C (3/8 : ℝ)*X^2 - C (1/4 : ℝ)*X^4
abbrev Q4 : ℝ[X] := C (129/8 : ℝ)*X^2 - C (183/4 : ℝ)*X^4 + 28*X^6 - 4*X^8
def A (n : ℕ) (p : ℝ[X]) := -p.derivative.derivative + 4*X*p.derivative - C (4*(n:ℝ))*p
def T (p : ℝ[X]) := X^2*p.derivative.derivative + (2*X-4*X^3)*p.derivative + (4*X^4-6*X^2)*p
abbrev R0 : ℝ[X] := C (81/32 : ℝ)*X^2 - C (167/16 : ℝ)*X^4 + 7*X^6-X^8
abbrev R4 : ℝ[X] := C (8643/32 : ℝ)*X^2 - C (26121/16 : ℝ)*X^4 + 2548*X^6-1354*X^8+264*X^10-16*X^12

theorem correction_zero : A 0 Q0 + T P0 + C (3/4 : ℝ)*P0 = 0 := by
  apply Polynomial.funext
  intro x
  norm_num [A,T,Q0,P0,derivative_mul,derivative_pow]
  <;> ring

theorem correction_four : A 4 Q4 + T P4 + C (43/4 : ℝ)*P4 = 0 := by
  apply Polynomial.funext
  intro x
  norm_num [A,T,Q4,P4,derivative_mul,derivative_pow]
  <;> ring

theorem residual_zero : T Q0 + C (3/4 : ℝ)*Q0 = R0 := by
  apply Polynomial.funext
  intro x
  norm_num [T,Q0,R0,derivative_mul,derivative_pow]
  <;> ring

theorem residual_four : T Q4 + C (43/4 : ℝ)*Q4 = R4 := by
  apply Polynomial.funext
  intro x
  norm_num [T,Q4,R4,derivative_mul,derivative_pow]
  <;> ring

theorem center_corrections : Q0.eval 0 = 0 ∧ Q4.eval 0 = 0 := by
  norm_num [Q0,Q4]
#print axioms correction_zero
#print axioms correction_four
#print axioms residual_zero
#print axioms residual_four
#print axioms center_corrections

def gaussianPoly (p : ℝ[X]) (t : ℝ) : ℝ := Real.exp (-t^2)*p.eval t
def gaussianDerivative (p : ℝ[X]) : ℝ[X] := p.derivative-2*X*p

theorem gaussianPoly_hasDerivAt (p : ℝ[X]) (t : ℝ) :
    HasDerivAt (gaussianPoly p) (gaussianPoly (gaussianDerivative p) t) t := by
  have he := (((hasDerivAt_id t).pow 2).neg).exp
  have h := he.mul (p.hasDerivAt t)
  convert h using 1 <;> simp [gaussianPoly, gaussianDerivative] <;> ring

theorem deriv_gaussianPoly (p : ℝ[X]) :
    deriv (gaussianPoly p) = gaussianPoly (gaussianDerivative p) := by
  funext t
  exact (gaussianPoly_hasDerivAt p t).deriv

theorem oscillator_conjugation (p : ℝ[X]) (n : ℕ) (t : ℝ) :
    -deriv (deriv (gaussianPoly p)) t + 4*t^2*gaussianPoly p t -
      (4*(n:ℝ)+2)*gaussianPoly p t = gaussianPoly (A n p) t := by
  rw [deriv_gaussianPoly,deriv_gaussianPoly]
  simp [gaussianPoly,gaussianDerivative,A,derivative_mul]
  ring

theorem perturbation_conjugation (p : ℝ[X]) (t : ℝ) :
    deriv (fun x => x^2*deriv (gaussianPoly p) x) t = gaussianPoly (T p) t := by
  have h := ((hasDerivAt_id t).pow 2).mul
    (gaussianPoly_hasDerivAt (gaussianDerivative p) t)
  rw [deriv_gaussianPoly]
  have hd : deriv (fun x => x^2*gaussianPoly (gaussianDerivative p) x) t =
      2*t*gaussianPoly (gaussianDerivative p) t +
        t^2*gaussianPoly (gaussianDerivative (gaussianDerivative p)) t := by
    simpa using h.deriv
  rw [hd]
  simp [gaussianPoly,gaussianDerivative,T,derivative_mul]
  ring

#print axioms gaussianPoly_hasDerivAt
#print axioms oscillator_conjugation
#print axioms perturbation_conjugation

def perturbedOscillator (n : ℕ) (eps beta : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (-deriv (deriv f) t + 4*t^2*f t - (4*(n:ℝ)+2)*f t) +
    eps*deriv (fun x => x^2*deriv f x) t - eps*beta*f t

theorem corrected_residual_zero (eps t : ℝ) :
    perturbedOscillator 0 eps (-(3/4)) (gaussianPoly (P0+C eps*Q0)) t =
      eps^2*gaussianPoly R0 t := by
  unfold perturbedOscillator
  rw [oscillator_conjugation,perturbation_conjugation]
  norm_num [gaussianPoly,A,T,P0,Q0,R0,derivative_mul,derivative_pow]
  <;> ring

theorem corrected_residual_four (eps t : ℝ) :
    perturbedOscillator 4 eps (-(43/4)) (gaussianPoly (P4+C eps*Q4)) t =
      eps^2*gaussianPoly R4 t := by
  unfold perturbedOscillator
  rw [oscillator_conjugation,perturbation_conjugation]
  norm_num [gaussianPoly,A,T,P4,Q4,R4,derivative_mul,derivative_pow]
  <;> ring
#print axioms corrected_residual_zero
#print axioms corrected_residual_four

def scaledGaussian (p : ℝ[X]) (c x : ℝ) := gaussianPoly p (c*x)
theorem scaledGaussian_hasDerivAt (p : ℝ[X]) (c x : ℝ) :
    HasDerivAt (scaledGaussian p c) (c*scaledGaussian (gaussianDerivative p) c x) x := by
  have h := (gaussianPoly_hasDerivAt p (c*x)).comp x ((hasDerivAt_id x).const_mul c)
  convert h using 1 <;> simp [scaledGaussian] <;> ring

theorem deriv_scaledGaussian (p : ℝ[X]) (c : ℝ) :
    deriv (scaledGaussian p c) = fun x => c*scaledGaussian (gaussianDerivative p) c x := by
  funext x
  exact (scaledGaussian_hasDerivAt p c x).deriv

theorem second_scaledGaussian (p : ℝ[X]) (c x : ℝ) :
    deriv (deriv (scaledGaussian p c)) x =
      c^2*scaledGaussian (gaussianDerivative (gaussianDerivative p)) c x := by
  rw [deriv_scaledGaussian]
  have h := (scaledGaussian_hasDerivAt (gaussianDerivative p) c x).const_mul c
  convert h.deriv using 1 <;> ring

def physicalResidual (n : ℕ) (m beta : ℝ) (f : ℝ → ℝ) (x : ℝ) :=
  -deriv (fun y => (1-y^2/m)*deriv f y) x +
    (4*Real.pi^2*x^2-(Real.pi*(4*(n:ℝ)+2)+beta/m))*f x

theorem physical_rescaling (p : ℝ[X]) (n : ℕ) (m beta x : ℝ) (hm : m ≠ 0) :
    physicalResidual n m beta (scaledGaussian p (Real.sqrt Real.pi)) x =
      Real.pi*perturbedOscillator n (1/(Real.pi*m)) beta (gaussianPoly p)
        (Real.sqrt Real.pi*x) := by
  let c := Real.sqrt Real.pi
  have hc : c^2=Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hd := (scaledGaussian_hasDerivAt (gaussianDerivative p) c x).const_mul c
  have hw : HasDerivAt (fun y : ℝ => 1-y^2/m) (-2*x/m) x := by
    convert (hasDerivAt_const x (1:ℝ)).sub (((hasDerivAt_id x).pow 2).div_const m) using 1 <;> simp <;> ring
  have hflux := hw.mul hd
  have heq : deriv (fun y => (1-y^2/m)*deriv (scaledGaussian p c) y) x =
      (-2*x/m)*(c*scaledGaussian (gaussianDerivative p) c x)+
      (1-x^2/m)*(c*(c*scaledGaussian (gaussianDerivative (gaussianDerivative p)) c x)) := by
    rw [deriv_scaledGaussian]
    exact hflux.deriv
  unfold physicalResidual
  change -deriv (fun y => (1-y^2/m)*deriv (scaledGaussian p c) y) x + _ = _
  rw [heq]
  unfold perturbedOscillator
  rw [deriv_gaussianPoly,deriv_gaussianPoly]
  have ht := perturbation_conjugation p (c*x)
  rw [deriv_gaussianPoly] at ht
  rw [ht]
  simp [scaledGaussian,gaussianPoly,gaussianDerivative,T,derivative_mul]
  field_simp
  simp only [show Real.sqrt Real.pi = c from rfl]
  rw [← hc]
  ring
#print axioms physical_rescaling

theorem physical_residual_zero (m x : ℝ) (hm : m ≠ 0) :
    physicalResidual 0 m (-(3/4))
      (scaledGaussian (P0+C (1/(Real.pi*m))*Q0) (Real.sqrt Real.pi)) x =
        gaussianPoly R0 (Real.sqrt Real.pi*x)/(Real.pi*m^2) := by
  rw [physical_rescaling _ _ _ _ _ hm,corrected_residual_zero]
  field_simp
  <;> ring

theorem physical_residual_four (m x : ℝ) (hm : m ≠ 0) :
    physicalResidual 4 m (-(43/4))
      (scaledGaussian (P4+C (1/(Real.pi*m))*Q4) (Real.sqrt Real.pi)) x =
        gaussianPoly R4 (Real.sqrt Real.pi*x)/(Real.pi*m^2) := by
  rw [physical_rescaling _ _ _ _ _ hm,corrected_residual_four]
  field_simp
  <;> ring
#print axioms physical_residual_zero
#print axioms physical_residual_four
end Q3QuasimodeCorrection
