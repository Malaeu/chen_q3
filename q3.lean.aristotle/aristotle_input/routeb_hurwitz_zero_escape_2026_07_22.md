# Aristotle request: local-domain Hurwitz zero escape

Create a new, independent Lean project.  Prove exactly one theorem and return
a single self-contained file `RouteBHurwitzZeroEscape.lean`.

Use Lean 4 with current Mathlib only.  The target below has local analyticity
on `U`; do not strengthen it to entire functions on all of `ℂ`.

```lean
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.OpenMapping

open Complex Filter Topology Set
open scoped Topology

noncomputable section

theorem routeB_hurwitz_zero_escape
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsPreconnected U)
    (g : ℕ → ℂ → ℂ) (h : ℂ → ℂ)
    (hg : ∀ k, AnalyticOnNhd ℂ (g k) U)
    (hconv : TendstoLocallyUniformlyOn g h atTop U)
    (hne : ∃ z ∈ U, h z ≠ 0)
    (hzf : ∀ k, ∀ z ∈ U, g k z ≠ 0) :
    ∀ z ∈ U, h z ≠ 0 := by
  -- prove this body
```

Requirements:

1. Preserve the theorem signature exactly.
2. Use `hUc`; disconnected-domain weakening is not accepted.
3. Do not introduce `axiom`, `sorry`, `admit`, `exact?`,
   `@[implemented_by]`, or `native_decide`.
4. Do not assume the limit is globally nonzero; use the supplied witness
   `hne` and analyticity/preconnectedness to exclude the identically-zero
   branch on `U`.
5. Do not state or prove RH, any H2a certificate, S1, S2, or a Route-B parent.
6. Add `#print axioms routeB_hurwitz_zero_escape`; only standard Mathlib
   foundations such as `propext`, `Classical.choice`, and `Quot.sound` are
   acceptable.
7. Report the exact success code
   `ROUTEB_HURWITZ_ZERO_ESCAPE_LEAN` only if the file builds with no holes.

The result is a formal complex-analysis component only.  It is not RH and does
not close the physical Route-B source obligations.  Its local receiver is the
upper/lower-half-strip refinement of
`Q3.RouteB.CanonicalRHRoute.rh_of_canonical_slots`; do not import or restate
that theorem.
