# Memo: Weil_criterion_tau0 vs classical Weil

Context: We currently use `Weil_criterion_tau0` in the main chain.
This is NOT the classical Weil criterion. It is a *stronger* (more demanding) axiom.

Why stronger:
- Classical Weil says: RH <-> Q >= 0 on the full Weil cone (all admissible test functions).
- `Weil_criterion_tau0` says: RH <-> Q >= 0 on a *restricted* cone
  (only functions approximable by Fejer x heat atoms with tau=0 and B in [B_min, B_max]).
- Positivity on a smaller test class does NOT automatically imply RH.
  So classical Weil does not imply `Weil_criterion_tau0` unless we prove
  that the restricted cone is sufficient (dense / universal).

What would be needed to justify tau0:
A) Show that every classical test function can be approximated by tau=0 atoms
   with the fixed B range [B_min, B_max]. This is unlikely / very strong.
OR
B) Enlarge the tau0 cone (e.g., allow B_max -> infinity or a growing range),
   then prove this enlarged cone is dense in the classical Weil cone.
   That becomes a new major analytic task.

Practical implication (Clay / external acceptance):
- If the requirement is the *classical* Weil criterion, then tau0 is a gap.
- If we keep tau0 as an axiom, the proof is conditional on a stronger criterion.
- We should clarify acceptance expectations before investing in tau0 justification.

Recommended short-term path:
- Keep `Weil_criterion_tau0` as explicit Tier-1 assumption.
- Close PrimeCert axioms: `prime_b_grid_bounds_data` and `prime_heat_bounds_data`.
- Later decide whether to replace tau0 with classical Weil by proving sufficiency.

Notes:
- The main chain currently uses `Weil_criterion_tau0` in Q3/Main.lean.
- The restriction is mainly the fixed B range, not just tau=0.
