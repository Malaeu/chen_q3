import Q3.Proofs.WeilCoreTau0_CriterionTau0
import Q3.Proofs.WeilCoreTau0_CounterexampleAmplifier

/-!
Q3.CheckContracts
=================

Fast contract sanity checks:
- negative results that intentionally falsify impossible bridges,
- axiom snapshots for current compact-approx theorem routes.
-/

namespace Q3.CheckContracts

-- 1) Constructive compact-approx route (sanity snapshot).
#print axioms Q3.Proofs.WeilCoreTau0.criterion_of_global_weil_and_compact_approx
#print axioms Q3.Proofs.WeilCoreTau0.criterion_on_weil_cone_tau0_of_compact_approx

-- 2) Amplifier route snapshots.
#print axioms Q3.Proofs.WeilCoreTau0.criterion_via_axiomatic_amplifier
#print axioms Q3.Proofs.WeilCoreTau0.criterion_via_compact_approx_amplifier

end Q3.CheckContracts
