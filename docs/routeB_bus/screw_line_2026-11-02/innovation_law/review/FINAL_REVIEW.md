# Bounded final read-only review

DIAGNOSTIC_NEVER_A_PROOF. Scope: RESULT.md, CARDS.md, main scan/analysis,
control-world code and validation against retained outputs and the pinned
source. Reviewed-input hashes are in final_review_inputs.json. Pending hinge
outputs are outside this review; no claim that those runs completed is made here.

Verdict: no scientific blocker found in the reviewed computations or principal
claims. One boundary wording correction was requested: the smooth control
removes **all prime-power atoms n>=2, including the atom at log2**, and replaces
them by exp(s/2)ds on [log2,infinity). The phrase "atoms above log2" in the
reviewed RESULT is ambiguous about that first atom. The actual code agrees
with CONTROL_PREREGISTRATION.md. This correction changes no calculation.

Checks performed:

- Both precision tables have exactly1,536 rows for each world at mesh256;
  all cumulative negative indices agree. The report's maximum relative
  precision differences match core/analysis.json.
- The maximum direct first-negative-witness relative error over the primary
  cells is6.22752831991e-96, consistent with the report's6.23e-96.
- Independently generated `true_zeta` controls agree with core innovations
  to relative1.17e-98 or better on meshes32 and64. Their code imports the
  previous Suzuki source implementation, while the new core has its own
  source implementation.
- The smooth integral in control_worlds.py equals the registered
  integral fromlog2 tot of exp(s/2)(t-s)ds. The two atomic controls retain
  nonnegative prime-power coefficients but are correctly not advertised as
  completed L-functions with a functional equation.
- The exponential-law failure uses the intervals and thresholds recorded
  before calculation. It is a rejection of the finite four-mesh test;
  the text correctly leaves possible eventual asymptotic convergence open.
- The Euler-cone counterexample uses the actual stationary minimizer with
  positive past at t=1. It is not an arbitrary residual. Its quoted Q(log2)
  values and the89-positive/9-negative count at mesh64,t=6 match the data.
- The root text distinguishes coefficient sensitivity, fixed-history time
  kinks, and adding a new grid observation. It does not use a later positive
  signed pivot to erase previous negative inertia.
- The planted hazard is correctly restricted to its finite-rank source
  modification. It is not advertised as a finite-rank model of DH or an
  unconditional zeta positivity estimate. Its floating precision and separate
  arbitrary-precision spot controls remain explicit.

The report closes the bounded experiment without claiming a new source law,
RH, or route promotion. Finite positivity, arbitrary-precision replay and
these code checks do not provide an infinite-history arithmetic bound.
