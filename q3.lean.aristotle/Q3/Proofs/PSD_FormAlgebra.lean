/-
PSD form algebra for the corrected positive-definite route.

This lightweight module records the finite-form algebra behind the fallback
`PSD-pd` route without importing the heavy Q3 analytic stack:

  arch floor + prime cap + cap <= floor  ==>  arch - prime is nonnegative.

Later bridge files can instantiate `qA`, `qP`, and `qDiff` with the concrete
Rayleigh quotients coming from Q3 matrices.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option linter.mathlibStandardSet false

namespace Q3.Proofs

/-- Positive semidefiniteness for an abstract finite quadratic form. -/
def FormPSD {ι : Type*} [Zero (ι → ℝ)] (q : (ι → ℝ) → ℝ) : Prop :=
  ∀ v : ι → ℝ, v ≠ 0 → 0 ≤ q v

/-- Difference of two real forms. -/
def formDiff {ι : Type*} (qA qP : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  fun v => qA v - qP v

/-- One-vector domination: an Archimedean lower bound and a prime upper bound
make the difference form nonnegative when the cap is no larger than the floor. -/
lemma formDiff_nonneg_of_floor_cap {ι : Type*}
    (qA qP : (ι → ℝ) → ℝ) (v : ι → ℝ)
    {floor cap : ℝ}
    (hA : floor ≤ qA v)
    (hP : qP v ≤ cap)
    (hcap : cap ≤ floor) :
    0 ≤ formDiff qA qP v := by
  unfold formDiff
  linarith

/-- Finite PSD-pd contract: if every nonzero vector sees an Archimedean floor
and a prime cap below that floor, then the difference form is PSD. -/
theorem formPSD_diff_of_uniform_floor_cap {ι : Type*} [Zero (ι → ℝ)]
    (qA qP : (ι → ℝ) → ℝ)
    {floor cap : ℝ}
    (hA : ∀ v : ι → ℝ, v ≠ 0 → floor ≤ qA v)
    (hP : ∀ v : ι → ℝ, v ≠ 0 → qP v ≤ cap)
    (hcap : cap ≤ floor) :
    FormPSD (formDiff qA qP) := by
  intro v hv
  exact formDiff_nonneg_of_floor_cap
    (qA := qA) (qP := qP) (v := v) (hA v hv) (hP v hv) hcap

/-- Strict-margin version of `formPSD_diff_of_uniform_floor_cap`. -/
theorem formPSD_diff_of_strict_uniform_floor_cap {ι : Type*} [Zero (ι → ℝ)]
    (qA qP : (ι → ℝ) → ℝ)
    {floor cap : ℝ}
    (hA : ∀ v : ι → ℝ, v ≠ 0 → floor ≤ qA v)
    (hP : ∀ v : ι → ℝ, v ≠ 0 → qP v ≤ cap)
    (hcap : cap < floor) :
    FormPSD (formDiff qA qP) := by
  exact formPSD_diff_of_uniform_floor_cap
    (qA := qA) (qP := qP) (floor := floor) (cap := cap) hA hP (le_of_lt hcap)

/-- Uniform explicit margin form. -/
theorem formDiff_margin_of_uniform_floor_cap {ι : Type*}
    (qA qP : (ι → ℝ) → ℝ)
    {floor cap : ℝ}
    (hA : ∀ v : ι → ℝ, floor ≤ qA v)
    (hP : ∀ v : ι → ℝ, qP v ≤ cap) :
    ∀ v : ι → ℝ, floor - cap ≤ formDiff qA qP v := by
  intro v
  unfold formDiff
  linarith [hA v, hP v]

/-- Nonnegativity of a finite form on a constrained subspace/predicate.

This is the lightweight interface needed for boundary-null reductions:
`Boundary v` can encode constraints such as `H_v(1/2)=H_v(-1/2)=0`. -/
def FormNonnegOn {ι : Type*} (q : (ι → ℝ) → ℝ)
    (Boundary : (ι → ℝ) → Prop) : Prop :=
  ∀ v : ι → ℝ, Boundary v → 0 ≤ q v

/-- Prime-graph SOS certificate form:

`qA + qLap - 2 W qG`.

Analytically this represents
`Arch energy + prime graph Laplacian energy - mass penalty`. -/
def primeGraphCert {ι : Type*}
    (qA qLap qG : (ι → ℝ) → ℝ) (W : ℝ) : (ι → ℝ) → ℝ :=
  fun v => qA v + qLap v - 2 * W * qG v

/-- Algebraic rewrite behind the prime-graph SOS trick.

If the prime form satisfies
`qP v = 2 W qG v - qLap v`, then the Arch-minus-prime form equals
`qA v + qLap v - 2 W qG v`. -/
lemma formDiff_eq_primeGraphCert_of_prime_sos {ι : Type*}
    (qA qP qLap qG : (ι → ℝ) → ℝ) (W : ℝ) (v : ι → ℝ)
    (hsos : qP v = 2 * W * qG v - qLap v) :
    formDiff qA qP v = primeGraphCert qA qLap qG W v := by
  unfold formDiff primeGraphCert
  linarith

/-- A spectral-gap inequality is exactly nonnegativity of the prime-graph
certificate form. -/
lemma primeGraphCert_nonneg_of_spectral_gap {ι : Type*}
    (qA qLap qG : (ι → ℝ) → ℝ) (W : ℝ) (v : ι → ℝ)
    (hgap : 2 * W * qG v ≤ qA v + qLap v) :
    0 ≤ primeGraphCert qA qLap qG W v := by
  unfold primeGraphCert
  linarith

/-- Boundary-null prime-graph certificate.

This is the abstract Lean landing surface for Step 8:
on the boundary-null predicate, the prime SOS identity plus the projected
spectral-gap certificate proves nonnegativity of `qA - qP`. -/
theorem formNonnegOn_diff_of_primeGraph_cert {ι : Type*}
    (qA qP qLap qG : (ι → ℝ) → ℝ) (W : ℝ)
    (Boundary : (ι → ℝ) → Prop)
    (hsos : ∀ v : ι → ℝ, Boundary v →
      qP v = 2 * W * qG v - qLap v)
    (hcert : ∀ v : ι → ℝ, Boundary v →
      0 ≤ primeGraphCert qA qLap qG W v) :
    FormNonnegOn (formDiff qA qP) Boundary := by
  intro v hv
  rw [formDiff_eq_primeGraphCert_of_prime_sos
    (qA := qA) (qP := qP) (qLap := qLap) (qG := qG) (W := W)
    (v := v) (hsos v hv)]
  exact hcert v hv

/-- Boundary-null prime-graph spectral-gap certificate.

This packages the target inequality
`qA v + qLap v >= 2 W qG v` on the boundary-null subspace. -/
theorem formNonnegOn_diff_of_primeGraph_gap {ι : Type*}
    (qA qP qLap qG : (ι → ℝ) → ℝ) (W : ℝ)
    (Boundary : (ι → ℝ) → Prop)
    (hsos : ∀ v : ι → ℝ, Boundary v →
      qP v = 2 * W * qG v - qLap v)
    (hgap : ∀ v : ι → ℝ, Boundary v →
      2 * W * qG v ≤ qA v + qLap v) :
    FormNonnegOn (formDiff qA qP) Boundary := by
  apply formNonnegOn_diff_of_primeGraph_cert
    (qA := qA) (qP := qP) (qLap := qLap) (qG := qG)
    (W := W) (Boundary := Boundary) hsos
  intro v hv
  exact primeGraphCert_nonneg_of_spectral_gap
    (qA := qA) (qLap := qLap) (qG := qG) (W := W)
    (v := v) (hgap v hv)

/-- Unconstrained version of the prime-graph certificate for ordinary PSD. -/
theorem formPSD_diff_of_primeGraph_cert {ι : Type*} [Zero (ι → ℝ)]
    (qA qP qLap qG : (ι → ℝ) → ℝ) (W : ℝ)
    (hsos : ∀ v : ι → ℝ, qP v = 2 * W * qG v - qLap v)
    (hcert : ∀ v : ι → ℝ, v ≠ 0 →
      0 ≤ primeGraphCert qA qLap qG W v) :
    FormPSD (formDiff qA qP) := by
  intro v hv
  rw [formDiff_eq_primeGraphCert_of_prime_sos
    (qA := qA) (qP := qP) (qLap := qLap) (qG := qG) (W := W)
    (v := v) (hsos v)]
  exact hcert v hv

/-- Algebraic rewrite for the prime-main/fluctuation split.

If `qP = qMain + qFluct`, then `qA - qP` is
`(qA - qFluct) - qMain`.  In the intended application `qMain <= 0` on the
boundary-null subspace, so `-qMain` is a bonus positive term. -/
lemma formDiff_eq_fluctuation_minus_main_of_split {ι : Type*}
    (qA qP qMain qFluct : (ι → ℝ) → ℝ) (v : ι → ℝ)
    (hsplit : qP v = qMain v + qFluct v) :
    formDiff qA qP v = formDiff qA qFluct v - qMain v := by
  unfold formDiff
  linarith

/-- One-vector main-kernel split certificate.

If the continuous main part is nonpositive and the Archimedean form dominates
the fluctuation, then the Archimedean form dominates the full prime form. -/
lemma formDiff_nonneg_of_main_nonpos_fluctuation_nonneg {ι : Type*}
    (qA qP qMain qFluct : (ι → ℝ) → ℝ) (v : ι → ℝ)
    (hsplit : qP v = qMain v + qFluct v)
    (hmain : qMain v ≤ 0)
    (hfluct : 0 ≤ formDiff qA qFluct v) :
    0 ≤ formDiff qA qP v := by
  rw [formDiff_eq_fluctuation_minus_main_of_split
    (qA := qA) (qP := qP) (qMain := qMain) (qFluct := qFluct)
    (v := v) hsplit]
  linarith

/-- Boundary-null main-kernel split certificate.

This is the abstract Lean landing surface for Step 9:
`qMain` models the continuous prime-main kernel `P0`, which is nonpositive on
the boundary-null subspace by the Green identity.  It remains to prove the
fluctuation domination `qA - qFluct >= 0`. -/
theorem formNonnegOn_diff_of_main_nonpos_fluctuation {ι : Type*}
    (qA qP qMain qFluct : (ι → ℝ) → ℝ)
    (Boundary : (ι → ℝ) → Prop)
    (hsplit : ∀ v : ι → ℝ, Boundary v →
      qP v = qMain v + qFluct v)
    (hmain : ∀ v : ι → ℝ, Boundary v → qMain v ≤ 0)
    (hfluct : FormNonnegOn (formDiff qA qFluct) Boundary) :
    FormNonnegOn (formDiff qA qP) Boundary := by
  intro v hv
  exact formDiff_nonneg_of_main_nonpos_fluctuation_nonneg
    (qA := qA) (qP := qP) (qMain := qMain) (qFluct := qFluct)
    (v := v) (hsplit v hv) (hmain v hv) (hfluct v hv)

/-- Unconstrained main-kernel split certificate for ordinary PSD. -/
theorem formPSD_diff_of_main_nonpos_fluctuation {ι : Type*} [Zero (ι → ℝ)]
    (qA qP qMain qFluct : (ι → ℝ) → ℝ)
    (hsplit : ∀ v : ι → ℝ, qP v = qMain v + qFluct v)
    (hmain : ∀ v : ι → ℝ, qMain v ≤ 0)
    (hfluct : FormPSD (formDiff qA qFluct)) :
    FormPSD (formDiff qA qP) := by
  intro v hv
  exact formDiff_nonneg_of_main_nonpos_fluctuation_nonneg
    (qA := qA) (qP := qP) (qMain := qMain) (qFluct := qFluct)
    (v := v) (hsplit v) (hmain v) (hfluct v hv)

/-- Base energy after removing the continuous prime-main kernel. -/
def fluctuationBase {ι : Type*}
    (qA qMain : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  formDiff qA qMain

/-- Main/fluctuation split rewritten through the base energy
`R = A - main`.

If `qP = qMain + qFluct`, then `qA - qP = R - qFluct`. -/
lemma formDiff_eq_base_minus_fluct_of_split {ι : Type*}
    (qA qP qMain qFluct : (ι → ℝ) → ℝ) (v : ι → ℝ)
    (hsplit : qP v = qMain v + qFluct v) :
    formDiff qA qP v = formDiff (fluctuationBase qA qMain) qFluct v := by
  simp [formDiff, fluctuationBase, hsplit]
  linarith

/-- One-vector fluctuation domination certificate:
if `R = A - main` dominates the fluctuation, then `A` dominates the full prime
form `main + fluctuation`. -/
lemma formDiff_nonneg_of_fluctuation_le_base {ι : Type*}
    (qA qP qMain qFluct : (ι → ℝ) → ℝ) (v : ι → ℝ)
    (hsplit : qP v = qMain v + qFluct v)
    (hdom : qFluct v ≤ fluctuationBase qA qMain v) :
    0 ≤ formDiff qA qP v := by
  rw [formDiff_eq_base_minus_fluct_of_split
    (qA := qA) (qP := qP) (qMain := qMain) (qFluct := qFluct)
    (v := v) hsplit]
  unfold formDiff
  exact sub_nonneg.mpr hdom

/-- Boundary-null fluctuation domination certificate.

This is the sharper Step 10 interface:
after the prime split `P = P0 + Pnu`, prove only `Pnu <= A - P0` on the
boundary-null subspace. -/
theorem formNonnegOn_diff_of_fluctuation_le_base {ι : Type*}
    (qA qP qMain qFluct : (ι → ℝ) → ℝ)
    (Boundary : (ι → ℝ) → Prop)
    (hsplit : ∀ v : ι → ℝ, Boundary v →
      qP v = qMain v + qFluct v)
    (hdom : ∀ v : ι → ℝ, Boundary v →
      qFluct v ≤ fluctuationBase qA qMain v) :
    FormNonnegOn (formDiff qA qP) Boundary := by
  intro v hv
  exact formDiff_nonneg_of_fluctuation_le_base
    (qA := qA) (qP := qP) (qMain := qMain) (qFluct := qFluct)
    (v := v) (hsplit v hv) (hdom v hv)

/-- Relative fluctuation certificate with a contraction factor.

If `qBase >= 0`, `qFluct <= theta*qBase`, and `theta <= 1`, then
`qFluct <= qBase`. -/
lemma fluctuation_le_base_of_relative_bound {ι : Type*}
    (qA qMain qFluct : (ι → ℝ) → ℝ) (theta : ℝ) (v : ι → ℝ)
    (hbase : 0 ≤ fluctuationBase qA qMain v)
    (hfluct : qFluct v ≤ theta * fluctuationBase qA qMain v)
    (htheta : theta ≤ 1) :
    qFluct v ≤ fluctuationBase qA qMain v := by
  have hmul : theta * fluctuationBase qA qMain v ≤
      1 * fluctuationBase qA qMain v := by
    exact mul_le_mul_of_nonneg_right htheta hbase
  linarith

/-- Boundary-null relative fluctuation domination certificate.

This matches the generalized-eigenvalue target
`lambda_max(Pnu, R) <= theta <= 1`. -/
theorem formNonnegOn_diff_of_relative_fluctuation_bound {ι : Type*}
    (qA qP qMain qFluct : (ι → ℝ) → ℝ)
    (Boundary : (ι → ℝ) → Prop) (theta : ℝ)
    (hsplit : ∀ v : ι → ℝ, Boundary v →
      qP v = qMain v + qFluct v)
    (hbase : ∀ v : ι → ℝ, Boundary v →
      0 ≤ fluctuationBase qA qMain v)
    (hfluct : ∀ v : ι → ℝ, Boundary v →
      qFluct v ≤ theta * fluctuationBase qA qMain v)
    (htheta : theta ≤ 1) :
    FormNonnegOn (formDiff qA qP) Boundary := by
  apply formNonnegOn_diff_of_fluctuation_le_base
    (qA := qA) (qP := qP) (qMain := qMain) (qFluct := qFluct)
    (Boundary := Boundary) hsplit
  intro v hv
  exact fluctuation_le_base_of_relative_bound
    (qA := qA) (qMain := qMain) (qFluct := qFluct)
    (theta := theta) (v := v) (hbase v hv) (hfluct v hv) htheta

/-- Absolute relative fluctuation certificate.

Step 11 rewrites the prime fluctuation through a smoothed error kernel.  A
typical analytic output is an absolute estimate
`|qFluct v| <= theta * R v`, where `R = qA - qMain`.  This lemma turns that
two-sided estimate into the one-sided domination required by Step 10. -/
lemma fluctuation_le_base_of_abs_relative_bound {ι : Type*}
    (qA qMain qFluct : (ι → ℝ) → ℝ) (theta : ℝ) (v : ι → ℝ)
    (hbase : 0 ≤ fluctuationBase qA qMain v)
    (habound : |qFluct v| ≤ theta * fluctuationBase qA qMain v)
    (htheta : theta ≤ 1) :
    qFluct v ≤ fluctuationBase qA qMain v := by
  have hfluct : qFluct v ≤ theta * fluctuationBase qA qMain v :=
    (abs_le.mp habound).2
  exact fluctuation_le_base_of_relative_bound
    (qA := qA) (qMain := qMain) (qFluct := qFluct)
    (theta := theta) (v := v) hbase hfluct htheta

/-- Boundary-null absolute relative fluctuation certificate.

This is the Lean landing surface for the Step 11 smoothed-error target:
if the arithmetic fluctuation has relative absolute norm at most
`theta <= 1` with respect to `R = A - P0`, then the full Arch-minus-prime
form is nonnegative on the constrained subspace. -/
theorem formNonnegOn_diff_of_abs_relative_fluctuation_bound {ι : Type*}
    (qA qP qMain qFluct : (ι → ℝ) → ℝ)
    (Boundary : (ι → ℝ) → Prop) (theta : ℝ)
    (hsplit : ∀ v : ι → ℝ, Boundary v →
      qP v = qMain v + qFluct v)
    (hbase : ∀ v : ι → ℝ, Boundary v →
      0 ≤ fluctuationBase qA qMain v)
    (habound : ∀ v : ι → ℝ, Boundary v →
      |qFluct v| ≤ theta * fluctuationBase qA qMain v)
    (htheta : theta ≤ 1) :
    FormNonnegOn (formDiff qA qP) Boundary := by
  apply formNonnegOn_diff_of_fluctuation_le_base
    (qA := qA) (qP := qP) (qMain := qMain) (qFluct := qFluct)
    (Boundary := Boundary) hsplit
  intro v hv
  exact fluctuation_le_base_of_abs_relative_bound
    (qA := qA) (qMain := qMain) (qFluct := qFluct)
    (theta := theta) (v := v) (hbase v hv) (habound v hv) htheta

end Q3.Proofs
