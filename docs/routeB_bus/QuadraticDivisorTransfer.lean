import Q3.Proofs.RouteB.ZeroEscapeLogic

set_option linter.mathlibStandardSet false

open Set

noncomputable section

namespace Q3.RouteB

/-- The final divisor step of `SOFT_2_QuadraticDivisorTransfer`.

The analytic Montel/Hurwitz and distributional-uniqueness work is represented
by the already obtained limit functions `F`, `Fsharp` and the pointwise
product identity.  This theorem checks that the types and zero transfer at
the last arrow are correct. -/
theorem quadraticDivisorTransfer_core
    (S : Set ℂ)
    (Xi gamma T Tsharp F Fsharp : ℂ → ℂ)
    (c : ℂ)
    (hF : ZerosRealOn S F)
    (hFsharp : ZerosRealOn S Fsharp)
    (hT : ∀ z ∈ S, T z = Xi z * gamma z)
    (hprod : ∀ z ∈ S, F z * Fsharp z = c * (T z * Tsharp z)) :
    ZerosRealOn S Xi := by
  intro z hz hXi
  have hTzero : T z = 0 := by
    rw [hT z hz, hXi]
    simp
  have hleft : F z * Fsharp z = 0 := by
    rw [hprod z hz, hTzero]
    simp
  rcases mul_eq_zero.mp hleft with hFzero | hFsharpzero
  · exact hF z hz hFzero
  · exact hFsharp z hz hFsharpzero

/-- A holomorphic multiplier preserves the target zero set exactly iff it is
nonvanishing.  This is the precise zero-free `gamma_0` divisor slot used by
plant P4. -/
theorem target_zero_iff_xi_zero_of_gamma_ne_zero
    (S : Set ℂ) (Xi gamma T : ℂ → ℂ)
    (hgamma : ∀ z ∈ S, gamma z ≠ 0)
    (hT : ∀ z ∈ S, T z = Xi z * gamma z)
    {z : ℂ} (hz : z ∈ S) :
    T z = 0 ↔ Xi z = 0 := by
  rw [hT z hz, mul_eq_zero]
  simp [hgamma z hz]

/-- Multiplying `F` and `Fsharp` by reciprocal unit phases leaves their
Hermitian product unchanged.  This is plant P1 in theorem form. -/
theorem hermitianProduct_unitPhase_invariant
    (F Fsharp : ℂ → ℂ) (phase : ℂ)
    (hphase : phase ≠ 0) (z : ℂ) :
    (phase * F z) * (phase⁻¹ * Fsharp z) = F z * Fsharp z := by
  field_simp

#print axioms quadraticDivisorTransfer_core
#print axioms target_zero_iff_xi_zero_of_gamma_ne_zero
#print axioms hermitianProduct_unitPhase_invariant

end Q3.RouteB
