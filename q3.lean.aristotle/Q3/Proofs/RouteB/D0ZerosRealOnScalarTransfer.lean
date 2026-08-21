import Q3.Proofs.RouteB.ZeroEscapeLogic

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Q3.RouteB

/-!
# Zeros-real transfers along a nonzero scalar and along pointwise equality

`SIMPLE_EVEN_GROUND_TO_REAL_ZEROS:1` is recorded `MISMATCH` with the reason:
the reality theorem is proved for the concrete CCM family, while the slot is
stated for the abstract selected family. The bridge between the two is a value
identity of the form `selected = c · concrete` — exactly what
`D0RawTransformRowScaling.lean` reduces to a coefficient-row identity — and the
transfer of `ZerosRealOn` along it.

The transfers are proved here. `ZerosRealOn` sees only the zero set, a nonzero
scalar does not move the zero set, and pointwise equal functions share it. With
these, the mismatch reduces to the same single row identity the value crosswalk
already waits on: two chains funnel into one obligation.

What this does **not** do: it does not assert the value identity, does not
provide the scalar, and does not touch the recorded ledger status. The step
stays `MISMATCH` until the row identity exists.

LEDGER:
  CLOSES: []
  OPENS:  []
-/

/-- Reality of zeros transfers along pointwise equality on the set. -/
theorem zerosRealOn_congr {S : Set ℂ} {f g : ℂ → ℂ}
    (hfg : ∀ z ∈ S, f z = g z) (hf : ZerosRealOn S f) :
    ZerosRealOn S g := by
  intro z hz hgz
  exact hf z hz ((hfg z hz).trans hgz)

/-- **The scalar transfer.**  A nonzero scalar multiple has the same zero set,
so reality of zeros passes to it. -/
theorem zerosRealOn_smul {S : Set ℂ} {f : ℂ → ℂ} {c : ℂ}
    (hc : c ≠ 0) (hf : ZerosRealOn S f) :
    ZerosRealOn S (fun z => c * f z) := by
  intro z hz hcz
  exact hf z hz ((mul_eq_zero.mp hcz).resolve_left hc)

/-- The composite shape the mismatch reduces to: a function that agrees on the
set with a nonzero multiple of one whose zeros are real has real zeros. -/
theorem zerosRealOn_of_eq_smul {S : Set ℂ} {f g : ℂ → ℂ} {c : ℂ}
    (hc : c ≠ 0)
    (hval : ∀ z ∈ S, g z = c * f z)
    (hf : ZerosRealOn S f) :
    ZerosRealOn S g :=
  zerosRealOn_congr (fun z hz => (hval z hz).symm) (zerosRealOn_smul hc hf)

#print axioms zerosRealOn_congr
#print axioms zerosRealOn_smul
#print axioms zerosRealOn_of_eq_smul

end Q3.RouteB
