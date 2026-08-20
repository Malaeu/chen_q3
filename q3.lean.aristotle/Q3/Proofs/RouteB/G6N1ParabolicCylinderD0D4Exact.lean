import Q3.Proofs.RouteB.D0PstarExplicitCCMLimitFourier
import Mathlib.RingTheory.Polynomial.Hermite.Basic

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Polynomial

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# F72.1B — exact `D_0` and `D_4` at the project scale

Floor F72.1B of the L73.2 wall, marked `LEAN_READY` at cost 2/10 in the judge's
REQ-2026-08-20-I verdict
(`docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_20_I_MEIXNER_SCHAEFKE_F72_1_PARAMETER_CHAIN_2026-08-20.md`),
executed on the owner's explicit authorization.

Meixner–Schäfke Satz 9 approximates the spheroidal modes by parabolic cylinder
functions `D_{n-m}((2γ)^{1/2} z)`. With `γ = 2πλ²` and `z = x/λ` the argument
transports to `sqrt (4π) * x`, so only two instances are ever needed: `D_0` and
`D_4` at that argument.

CONVENTION LOCK, flagged by the judge as a `C04` trap. The identity is

```
D_n(t) = exp (-t²/4) · He_n(t) = 2^{-n/2} · exp (-t²/4) · H_n(t/√2)
```

with `He_n` the PROBABILISTS' and `H_n` the PHYSICISTS' Hermite polynomial.
Writing `2^{-n/2}` in front of a probabilists' `He_n` is wrong. Mathlib's
`Polynomial.hermite` is the probabilists' one — its recursion is
`He_{n+1} = X · He_n - He_n'` — so this file uses it with NO extra power of two.

No general parabolic-cylinder or spheroidal API is built here, and none is
needed: at these two orders the objects are polynomial times Gaussian.

LEDGER:
  CLOSES: [F72_1B_D0_D4_PHYSICAL_HERMITE_EXACT]
  OPENS:  []
-/

/-- Parabolic cylinder function at integer order, probabilists' convention:
`D_n(t) = exp (-t²/4) · He_n(t)`. -/
noncomputable def parabolicCylinderD (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-t ^ 2 / 4) * (Polynomial.aeval t (Polynomial.hermite n))

/-- The argument at which Satz 9 is consumed after `γ = 2πλ²` and `z = x/λ`. -/
noncomputable def projectCylinderArgument (x : ℝ) : ℝ :=
  Real.sqrt (4 * Real.pi) * x

private theorem sq_projectCylinderArgument (x : ℝ) :
    (projectCylinderArgument x) ^ 2 = 4 * Real.pi * x ^ 2 := by
  rw [projectCylinderArgument, mul_pow, Real.sq_sqrt (by positivity)]

private theorem hermite_zero_aeval (t : ℝ) :
    (Polynomial.aeval t (Polynomial.hermite 0)) = 1 := by
  simp [Polynomial.hermite_zero]

private theorem hermite_one_eq : Polynomial.hermite 1 = (X : Polynomial ℤ) := by
  show Polynomial.hermite (0 + 1) = _
  rw [Polynomial.hermite_succ, Polynomial.hermite_zero]
  simp

private theorem hermite_two_eq :
    Polynomial.hermite 2 = (X ^ 2 - 1 : Polynomial ℤ) := by
  show Polynomial.hermite (1 + 1) = _
  rw [Polynomial.hermite_succ, hermite_one_eq]
  simp [sq]

private theorem hermite_three_eq :
    Polynomial.hermite 3 = (X ^ 3 - 3 * X : Polynomial ℤ) := by
  show Polynomial.hermite (2 + 1) = _
  rw [Polynomial.hermite_succ, hermite_two_eq]
  simp
  ring

private theorem hermite_four_eq :
    Polynomial.hermite 4 = (X ^ 4 - 6 * X ^ 2 + 3 : Polynomial ℤ) := by
  show Polynomial.hermite (3 + 1) = _
  rw [Polynomial.hermite_succ, hermite_three_eq]
  simp
  ring

private theorem hermite_four_aeval (t : ℝ) :
    (Polynomial.aeval t (Polynomial.hermite 4)) = t ^ 4 - 6 * t ^ 2 + 3 := by
  rw [hermite_four_eq]
  simp [map_ofNat]

/-- `D_0` at the project argument is the plain Gaussian. -/
theorem parabolicCylinderD_zero_projectArgument (x : ℝ) :
    parabolicCylinderD 0 (projectCylinderArgument x) =
      Real.exp (-Real.pi * x ^ 2) := by
  rw [parabolicCylinderD, hermite_zero_aeval, mul_one,
    sq_projectCylinderArgument]
  ring_nf

/-- `D_4` at the project argument is the explicit quartic times the Gaussian. -/
theorem parabolicCylinderD_four_projectArgument (x : ℝ) :
    parabolicCylinderD 4 (projectCylinderArgument x) =
      Real.exp (-Real.pi * x ^ 2) *
        (16 * Real.pi ^ 2 * x ^ 4 - 24 * Real.pi * x ^ 2 + 3) := by
  rw [parabolicCylinderD, hermite_four_aeval, sq_projectCylinderArgument]
  have harg4 : (projectCylinderArgument x) ^ 4 =
      16 * Real.pi ^ 2 * x ^ 4 := by
    have : (projectCylinderArgument x) ^ 4 =
        ((projectCylinderArgument x) ^ 2) ^ 2 := by ring
    rw [this, sq_projectCylinderArgument]
    ring
  rw [harg4]
  have hexp : Real.exp (-(4 * Real.pi * x ^ 2) / 4) =
      Real.exp (-Real.pi * x ^ 2) := by
    congr 1
    ring
  rw [hexp]
  ring

/-- The exact decomposition of the literal CCM equation-(7.1) packet into the
two parabolic cylinder functions at the project argument.

The coefficient of `x²` matches on its own: fixing `1/16` from the quartic term
forces `-24π/16 = -3π/2`, which is exactly what the packet carries.  That
agreement is not imposed here, it falls out. -/
theorem explicitCCMLimitH_eq_cylinder_combination (x : ℝ) :
    explicitCCMLimitH x =
      (((1 / 16 : ℝ) * parabolicCylinderD 4 (projectCylinderArgument x) -
        (3 / 16 : ℝ) * parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ) := by
  rw [parabolicCylinderD_four_projectArgument,
    parabolicCylinderD_zero_projectArgument, explicitCCMLimitH]
  have hexp : Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) =
      ((Real.exp (-Real.pi * x ^ 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hexp]
  push_cast
  ring

#print axioms parabolicCylinderD
#print axioms projectCylinderArgument
#print axioms hermite_four_aeval
#print axioms parabolicCylinderD_zero_projectArgument
#print axioms parabolicCylinderD_four_projectArgument
#print axioms explicitCCMLimitH_eq_cylinder_combination

end Q3.RouteB.D0Pstar
