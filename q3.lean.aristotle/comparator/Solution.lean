/-
Solution.lean — the UNTRUSTED comparator solution module.

Proves the bridge statement of Challenge.lean by delegating to the project.
The Clay statement `RiemannHypothesis.riemannHypothesis` is deliberately ABSENT:
it enters this file only on the day the roof `Q3.rh_of_canonical_slots` is
unconditional, as `Q3.riemannHypothesis_of_rh <roof>`.  Until then a run of
`config-rh.json` fails, and that failure is the mechanical meaning of
`PX_RH_CLAIM: NOT_MADE`.
-/
import Q3.Proofs.RouteB.MathlibRiemannHypothesisBridge

namespace Q3Comparator

theorem rh_strip_iff_riemannHypothesis :
    (∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2) ↔ RiemannHypothesis :=
  Q3.rh_iff_mathlib

end Q3Comparator
