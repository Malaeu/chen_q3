/-
Challenge.lean — the TRUSTED comparator challenge module: WHAT IS CLAIMED.

Two statements, proofs `sorry` (deliberate: this is the challenge side).

1. `RiemannHypothesis.riemannHypothesis : RiemannHypothesis` — the Clay statement in
   Mathlib's own type, copied from google-deepmind/formal-conjectures
   `FormalConjectures/Millenium/RiemannHypothesis.lean` (attributes and the project
   util import stripped; nothing else changed).  This is the statement a PX_RH_CLAIM
   run must match.  Nothing under `Q3/` is needed to read it.

2. `Q3Comparator.rh_strip_iff_riemannHypothesis` — the project's strip form of RH
   (the body of `Q3.RH`, inlined here from Mathlib alone so that the trusted side
   imports nothing from the project) is equivalent to Mathlib's `RiemannHypothesis`.
   This is the consumer-side bridge; it is provable today.

github.com/leanprover/comparator checks that `Solution` proves exactly these
statements, uses only `propext`, `Classical.choice`, `Quot.sound`, and replays the
proofs through the kernel.  See README.md here.
-/
import Mathlib

namespace RiemannHypothesis

/-- The **Riemann Hypothesis**: all non-trivial zeros of the Riemann zeta function have real
part $\frac{1}{2}$. That is, if $\zeta(s) = 0$, $s \neq 1$, and $s$ is not a trivial zero
$-2(n+1)$ for some $n \in \mathbb{N}$, then $\operatorname{Re}(s) = \frac{1}{2}$.

This is the official Millennium Prize Problem as posed by the
[Clay Mathematics Institute](https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf).

This uses the `RiemannHypothesis` type from Mathlib, which is defined as
`∀ (s : ℂ), riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2`. -/
theorem riemannHypothesis : RiemannHypothesis := by
  sorry

end RiemannHypothesis

namespace Q3Comparator

/-- The project's strip form of RH (every zero of `riemannZeta` with `0 < Re s < 1` has
`Re s = 1/2`) is equivalent to Mathlib's `RiemannHypothesis`. -/
theorem rh_strip_iff_riemannHypothesis :
    (∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2) ↔ RiemannHypothesis := by
  sorry

end Q3Comparator
