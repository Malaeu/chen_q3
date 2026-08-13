# Goal 058 inversion/coefficient and denominator crosswalk closeout

Date: 2026-08-14

## Verdict

```yaml
TARGET_ID: GOAL058_INVERSION_COEFFICIENT_DENOMINATOR_CROSSWALK
VERDICT: PASS_EXACT_CROSSWALK_AND_FLOOR_BRIDGE
SUCCESS: GOAL058_INVERSION_COEFFICIENT_DENOMINATOR_CROSSWALK_PROVED
SCOPE: EXACT_ANALYTIC_TRANSPORT
VERIFIER: LEAN
LIMIT_PACKET: OPEN_SOURCE_CONSTRUCTION
ODD_MASS_RATE: OPEN_SOURCE_ESTIMATE
DENOMINATOR_FLOOR: OPEN_CONCRETE_INPUT
G1: OPEN
G3: OPEN
ROUTE: CHALLENGER_NOT_RH
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## Integrated theorem

```text
Q3/Proofs/RouteB/D0PstarInversionCoefficientCrosswalk.lean
```

The file proves three exact production bridges.

1. `inner_V_neg_eq_inner_V_of_inversion_even` transports the physical
   identity `g(u^-1) = g(u)` on the literal multiplicative window to the
   exact coefficient identity
   `inner(V_-n,g) = inner(V_n,g)`.  Its proof uses the existing `du/u -> dx`
   transport, reflection `x -> L-x`, and the exact integer phase
   `exp(2*pi*I*n)=1`; no coefficient symmetry is assumed.
2. `sourceCCMComplexOddMass_le_norm_sub_sq_of_inversion_even` applies that
   crosswalk directly to the literal normalized source row.  Any actual
   inversion-even ambient packet controls its source odd mass by the squared
   approximation error.
3. `norm_inner_V0_sub_approximation_error_le_projected_trial_norm` proves the
   denominator mechanism

   ```text
   ||<V_0,f>|| - ||gTrial_m-f|| <= ||P_(m,N) gTrial_m||.
   ```

   Thus a concrete comparison packet with nonzero central coefficient and a
   strictly smaller approximation error supplies the required positive
   normalization floor.  The theorem does not assume such a packet or floor.

## Production validation

```text
direct lake env lean: PASS
target lake build: PASS (7793 jobs)
q3_check: PASS
public theorem axioms: [propext, Classical.choice, Quot.sound]
```

The proof keeps the actual `V_n_m`, `gTrial_m`, `gTrial_m_N`, `kTrial_m_N`,
`E_star`, `dStar`, and `I_m` objects.  It introduces no alternate coefficient
row, symmetrized trial, source-field assumption, or finite diagnostic.

## Exact remaining source obligation

The crosswalk and floor algebra are now kernel checked, but their concrete
analytic input is not yet formalized.  The smallest source-faithful next
packet is:

1. define the explicit limiting Riemann function from CCM Eq. (7.1),
   `h(u) = (pi/2) u^2 (2*pi*u^2-3) exp(-pi*u^2)`;
2. prove that `E_star h` is inversion even, belongs to the required restricted
   `L2` space, and has a nonzero central logarithmic coefficient;
3. transport the CCM Lemmas 7.2--7.3 approximation estimate from the actual
   two-mode prolate trial to `E_star h` on the same family;
4. choose one precommitted cofinal `(m,N)` schedule on which the approximation
   error is below the central coefficient and the odd-mass rate tends to zero.

The first item ultimately needs a source-locked Poisson/Fourier proof for the
explicit polynomial Gaussian.  A generic inversion-even binder would only be
a receiver and would not close G3.

G1 is independent and remains at the literal source arithmetic wall: an
even-sector simplicity/gap supplier plus strict even/odd ground ordering, with
quantitative cofinal tracking.

## Exact evidence boundary

This closeout proves the missing inversion-to-coefficient crosswalk and the
exact denominator-floor mechanism.  It does not construct the limiting
packet, prove the CCM approximation rate, establish a positive denominator
for the source family, choose a cofinal schedule, prove G1 or G3, promote
Route B, or prove RH.

```yaml
SEARCH_FLAGS:
  - GOAL058_INVERSION_COEFFICIENT_CROSSWALK
  - GOAL058_PROJECTED_TRIAL_DENOMINATOR_FLOOR
  - GOAL058_EXPLICIT_RIEMANN_LIMIT_PACKET
  - GOAL058_POLYNOMIAL_GAUSSIAN_POISSON
ARSENAL_USED:
  - exact logarithmic-window measure transport
  - interval reflection
  - integer complex-exponential phase
  - projection orthogonality
  - Cauchy-Schwarz
REJECTED:
  - coefficient symmetry as an input
  - denominator positivity from TrialNonzero alone
  - source-row symmetrization
  - generic receiver as G3 closure
AUTOPSY: dropped=DEPENDENCY; note=Crosswalk and floor algebra are exact; the explicit inversion-even limit packet, approximation rate, and coupled cofinal schedule remain source obligations.
```
