# Goal 058 source CCM odd-mass reflection-defect closeout

Date: 2026-08-14

## Verdict

```yaml
TARGET_ID: GOAL058_SOURCE_CCM_ODD_MASS_REFLECTION_DEFECT
VERDICT: PASS_EXACT_REPRESENTATION_AND_RECEIVER
SUCCESS: GOAL058_SOURCE_CCM_ODD_MASS_REFLECTION_DEFECT_PROVED
SCOPE: FINITE_EXACT_REPRESENTATION
VERIFIER: LEAN
ODD_MASS_DECAY: OPEN_SOURCE_ESTIMATE
G1: OPEN
G3: OPEN
ROUTE: CHALLENGER_NOT_RH
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## Integrated theorem

```text
Q3/Proofs/RouteB/D0PstarSourceCCMOddMassReflectionDefect.lean
```

The file retains the literal normalized complex source row
`sourceCCMComplexRow`; it does not replace the row by a real part and does not
symmetrize it.  It defines

```text
q_-(j) = (q(j) - q(-j)) / 2
omega  = sum_j normSq(q_-(j))
```

and the finite synthesis of the reflected coefficient row.  The exact main
identity is

```text
omega = (1/4) * ||kTrial_m_N - reflectedFiniteTrial||^2.
```

The source-shaped receiver
`sourceCCMComplexOddMass_le_norm_sub_sq_of_even_coefficients` proves that any
ambient comparison packet whose retained coefficients satisfy the exact
reflection symmetry controls the whole literal odd mass by the squared
ambient approximation error.  The comparison packet is not manufactured and
the source row remains unchanged.

## Production validation

```text
direct lake env lean: PASS
target lake build: PASS (7790 jobs)
q3_check: PASS
forbidden sorry/admit/axiom scan: PASS
git diff --check: PASS
public theorem axioms: [propext, Classical.choice, Quot.sound]
```

The target build first caught an invalid local `set_option ... in
noncomputable def` form and downstream `sorryAx` contamination.  The rejected
heavy Hilbert-basis unitary was removed instead of hiding it behind a larger
heartbeat budget.  The accepted theorem uses only the finite reflected
synthesis that its statement needs.  The rebuilt target contains no
`sorryAx`.

## Source attack and exact remaining rate

The current `ProlatePair` exports only the center identities
`h0_fourier_center` and `h4_fourier_center`; it neither constructs the actual
PSWF modes nor exports their full restricted finite-Fourier eigenrelations.
The primary PSWF sources do contain the mathematical eigensystem, but its
exact project scaling, phase, and mode selection have not been transported to
Lean.

That missing eigenrelation would not by itself make the two-mode trial an
eigenfunction or prove multiplicative inversion symmetry.  The source-faithful
quantitative route instead uses CCM Lemmas 7.2--7.3:

```text
delta(lambda) = sup |h_lambda - h| <= c * lambda^-2
|E(h_lambda)(u) - E(h)(u)| <= lambda * delta(lambda) * u^-1/2
E(h)(u^-1) = E(h)(u).
```

At the paper level these imply the candidate window estimate

```text
||(E(h_lambda) - J E(h_lambda))/2||^2
  <= lambda^2 * delta(lambda)^2 * (lambda - lambda^-1)
  <= c^2 * (lambda^-1 - lambda^-3).
```

This is an identified source theorem shape, not yet a Lean theorem.  To reach
the normalized projected source row one still needs:

1. the exact inversion/reflection coefficient crosswalk for the production
   logarithmic modes;
2. contraction through the finite projection;
3. an eventual positive lower bound for `||P_(m,N) E(h_lambda)||` on the same
   precommitted schedule.

`TrialNonzero` gives only pointwise strict nonzeroness and cannot occupy the
third quantitative obligation.

## G1 discriminator

The parallel source audit returned
`NO_BETA_ONLY_SIMPLICITY_FACTOR`.  The exact rank-two commutator and
divided-difference off-diagonal formula admit the previously pinned exact Lean
`3 x 3` all-ones counterexample with a two-dimensional ground kernel.  At
`N = 1` the general
centrosymmetric source-shaped characteristic polynomial is

```text
(a - b - lambda) * ((a + b - lambda) * (c - lambda) - 2*b^2),
```

so the diagonal arithmetic is load-bearing.  A surviving parity/Krylov
decomposition would require a literal nonzero even-sector Krylov determinant
and the strict ordering `minSpec(T_+) < minSpec(T_-)`; neither follows from the
current `ccmBeta` facts.  Quantitative cofinal tracking would additionally need
lower bounds for those determinants or the resulting gap.

## Exact evidence boundary

This closeout proves a finite exact identity and a non-circular receiver.  It
does not prove odd-mass decay, a normalized projection denominator floor,
simple-even ground existence, a spectral gap, a cofinal schedule, G1, G3,
Route B promotion, or RH.

```yaml
SEARCH_FLAGS:
  - GOAL058_SOURCE_CCM_ODD_MASS_REFLECTION_DEFECT
  - GOAL058_ODD_MASS_INVERSION_DEFECT_RATE
  - GOAL058_NORMALIZED_PROJECTED_TRIAL_DENOMINATOR_FLOOR
  - GOAL058_EVEN_KRYLOV_DETERMINANT
ARSENAL_USED:
  - exact finite Fourier synthesis
  - coefficient reflection
  - Bessel inequality
  - primary-source PSWF and CCM scope audit
REJECTED:
  - exact odd mass equals zero from additive evenness
  - full Hilbert-basis unitary as necessary infrastructure
  - beta-only or commutator-only simplicity
  - finite diagnostic as cofinal supplier
AUTOPSY: dropped=DEPENDENCY; note=Odd mass now has an exact physical error receiver; source inversion-defect decay and normalization remain open.
```
