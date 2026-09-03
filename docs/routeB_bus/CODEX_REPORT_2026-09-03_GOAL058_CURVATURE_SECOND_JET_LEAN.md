# Codex report — Goal 058 curvature second-jet Lean bookkeeping

Date: 2026-09-03
Task: `docs/Codex/TASK_2026-09-03_goal058_curvature_second_jet_lean_bookkeeping.md`
Judge verdict: `0c0a2b37` (`RUN_RELATIVE_RITZ_DECISIVE_TEST`)
Rebased base: `e9545a19d1d5c9304e3cb254297144674b1e261f`
Branch: `codex_linux_app/goal058-curvature-second-jet`

```yaml
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
ROUTE_PROMOTION: false
PHASE_KEY_CHANGED: false
COFINAL_CURVATURE_BOUND_CLAIMED: false
NODE_CONSUMPTION_OR_CLOSE: false
```

The five ordered bookkeeping items were attempted in order.  Items 1--4 are
kernel-green.  Item 5 stops at the source-locked Mathlib boundary required by
the task; no replacement axiom, `sorry`, or surrogate factorization was added.

## Item 1 — `KERNEL_GREEN`

- File: `q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59EntireTransform.lean`
- Commit: `1dbe12e6` — `[Linux-Codex][rh_clean][Goal058] Prove Proposition 59 second jet`
- Declarations:
  - `Q3.RouteB.proposition59SecondJetCoefficient`
  - `Q3.RouteB.proposition59PoleKernel_secondDerivative_zero`
  - `Q3.RouteB.proposition59RawTransform_secondDerivative_zero`
- Result: the exact second derivative at zero is the requested central
  coefficient plus the erased reciprocal-square sum, with the common factor
  `-((L : ℂ)^2 * (Real.sqrt L : ℂ))`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.

## Item 2 — `KERNEL_GREEN`

- File: `q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59EntireTransform.lean`
- Commit: `79ed5cf7` — `[Linux-Codex][rh_clean][Goal058] Bound Proposition 59 second-jet functional`
- Declarations:
  - `Q3.RouteB.proposition59SecondJetFunctional_norm_sq_le_one_div_eighty`
  - `Q3.RouteB.proposition59SecondJetFunctional`
  - `Q3.RouteB.proposition59SecondJetFunctional_norm_le_one_div_sqrt_eighty`
  - `Q3.RouteB.proposition59RawTransform_secondDerivative_sub_norm_le`
- Result: the coefficient-functional squared norm is at most `1 / 80`; the
  requested second-jet stability bound follows by finite-dimensional
  Cauchy--Schwarz.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.

## Item 3 — `KERNEL_GREEN`

- File: `q3.lean.aristotle/Q3/Proofs/RouteB/RelativeRitzFinite.lean`
- Commit: `0fbb668e` — `[Linux-Codex][rh_clean][Goal058] Prove finite relative Ritz bound`
- Declaration:
  - `Q3.RouteB.hermitian_relative_ritz_projective_defect_le_rayleigh_excess_div_gap`
- Result: for a finite Hermitian matrix, a unit bottom eigenvector and an
  orthogonal Rayleigh floor at `lambda2`, the projective defect of a unit trial
  vector is bounded by its Rayleigh excess divided by `lambda2 - lambda1`.
  The existing trial-complement floor predicate was not modified.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.

## Item 4 — `KERNEL_GREEN`

- File: `q3.lean.aristotle/Q3/Proofs/RouteB/Goal058CurvatureArithmetic.lean`
- Commit: `f2ade91a` — `[Linux-Codex][rh_clean][Goal058] Prove curvature schedule arithmetic`
- Declarations:
  - `Q3.RouteB.goal058_schedule_log_sq_div_tendsto_zero`
  - `Q3.RouteB.one_div_nat_sq_tail_le_one_div`
  - `Q3.RouteB.forcedZeroCurvatureTail_le`
- Results:
  - `(Real.log (k + 2))^2 / (k + 2)` tends to zero along `atTop`;
  - the reciprocal-square tail beginning at `N + 1` is at most `1 / N`;
  - multiplying this estimate by `L^2 / (4 * Real.pi^2)` gives the requested
    forced-zero curvature contribution bound.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.

## Item 5 — `MATHLIB_GAP_NAMED`

Pinned toolchain:

- Lean: `leanprover/lean4:v4.26.0`
- Mathlib revision: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

Required but absent interface, fixed here as the exact gap identifier:

```text
Complex.hadamardFactorization_order_le_one
```

Required content: a theorem that turns an entire function of growth order at
most one into its Hadamard canonical product over the zero divisor, with the
degree-at-most-one exponential factor and convergence data exposed strongly
enough to pair real zeros for an even, real-on-real, normalized function.
Mathlib at the pinned revision also has no canonical predicate representing
the growth order of an entire function, so the premise `order <= 1` itself has
no existing declaration-level carrier to instantiate.

Exact source surface checked:

- `Mathlib/Analysis/Complex/Hadamard.lean` contains the Hadamard three-lines
  theorem, not Hadamard factorization;
- `Mathlib/Analysis/Complex/JensenFormula.lean` gives Jensen's formula and
  finite-ball divisor extraction, not a global canonical product;
- `Mathlib/Analysis/Complex/ValueDistribution/` provides counting and
  characteristic functions, but no order-one factorization theorem;
- repository-wide searches for `hadamard`, `canonical product`,
  `weierstrass product`, `entire function`, `finite order`, and
  `factorization` found no declaration with the required interface.

Consequently the requested inequality
`‖G z‖ ≤ Real.exp ((-G''(0) / 2) * ‖z‖^2)` was not stated as a new Lean axiom
and was not assigned `KERNEL_GREEN`.  The mathematical bridge remains a named
formalization dependency.

## Verification

Post-rebase checks:

```text
lake env lean Q3/Proofs/RouteB/Proposition59EntireTransform.lean       PASS
lake env lean Q3/Proofs/RouteB/RelativeRitzFinite.lean                 PASS
lake env lean Q3/Proofs/RouteB/Goal058CurvatureArithmetic.lean        PASS
lake build Q3.Proofs.RouteB.Proposition59EntireTransform
           Q3.Proofs.RouteB.RelativeRitzFinite
           Q3.Proofs.RouteB.Goal058CurvatureArithmetic                PASS
scripts/q3_check.sh Proposition59EntireTransform.lean                 PASS
scripts/q3_check.sh RelativeRitzFinite.lean                            PASS
scripts/q3_check.sh Goal058CurvatureArithmetic.lean                   PASS
orchestrator/spine.py --refresh --strict --reason semantic-index-refresh
  CONTROL_V10_STRICT_PASS                                             PASS
```

All reported public theorems use only the standard allowed axiom profile:
`propext`, `Classical.choice`, and `Quot.sound`.  No textual `sorry`, `admit`,
or `exact?` is present in the three owned Lean files.

## Remaining mathematical boundary

This bookkeeping does not prove `sup_k kappa_k < infinity`, does not establish
local boundedness of the tracked ground family, and does not discharge the
`hconv` hypothesis of
`Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi`.  Runtime production
consumption remains on `NODE_REGISTRY_EXACT_EDGE_REQUIRED`; the new theorems
are validated source candidates, not a route close or an RH claim.
