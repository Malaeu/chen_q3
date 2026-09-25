/-
Solution.lean — the UNTRUSTED comparator solution module.

Proves the bridge statement of Challenge.lean by delegating to the project.
The Clay statement `RiemannHypothesis.riemannHypothesis` is deliberately ABSENT:
it enters this file only on the day the canonical roof
`Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi`
(`Q3/Proofs/RouteB/Goal058DirectGroundZeroEscape.lean`) is discharged, i.e. one real-zero
entire family `F` with `hzeros`, `hentire`, `hconv` is constructed, as
`Q3.riemannHypothesis_of_rh (Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi F hzeros hentire hconv)`.
Canonical roof decided 2026-09-25 (owner order); the older 7-port roof
`Q3.rh_of_canonical_slots` is historical and no longer the target.  Until then a run of
`config-rh.json` fails, and that failure is the mechanical meaning of
`PX_RH_CLAIM: NOT_MADE`.
-/
import Q3.Proofs.RouteB.MathlibRiemannHypothesisBridge

namespace Q3Comparator

theorem rh_strip_iff_riemannHypothesis :
    (∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2) ↔ RiemannHypothesis :=
  Q3.rh_iff_mathlib

end Q3Comparator
