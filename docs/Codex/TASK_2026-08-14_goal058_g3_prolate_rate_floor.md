# Codex task — Goal 058 G3 prolate rate and floor

Date: 2026-08-14
Source commit: `0fb4023ab401ab3f68e1a507197e379e9261cc3c`

## Selected source front

Continue the owner-authorized Goal 058 G1/G3 closure loop at the remaining G3
source theorem. The explicit CCM Eq. (7.1) packet, its Fourier invariance, its
`E_star` inversion symmetry, the physical inversion-to-coefficient crosswalk,
and the denominator mechanism are already kernel checked.

The active obligation is to connect the actual normalized two-mode prolate
family to those consumers:

```text
actual h_lambda on current PairIndex family
  -> uniform CCM Lemma 7.2 O(lambda^-2) estimate to explicitCCMLimitH
  -> E_star/window approximation and nonzero central overlap
  -> eventual projected denominator floor
  -> one precommitted coupled (m,N) schedule
```

## Required evidence boundary

- Use the actual production `ProlatePair`, `hTrial_m`, `gTrial_m`, `P_m_N`,
  and `PairIndex` objects; do not introduce a parallel family with stronger
  fields and call it the source family.
- A theorem taking the approximation rate, central overlap, denominator floor,
  or cofinal tracking as binders is a receiver and does not close this task.
- Source-lock the normalization, phase, scaling, and degree `0/4` selection.
- Preserve the one-family invariant and the P59 `_normalized` supplier lock.
- Keep G1 open as the parallel spectral front. Beta/commutator identities alone
  do not imply simplicity or a positive uniform gap.
- No G3, Route B, or RH promotion before the actual rate, floor, and coupled
  schedule are kernel checked.

## First action

Audit the current `ProlatePair`/constructor surface against CCM Lemma 7.2 and
its pinned primary source. Identify the smallest missing source constructor or
theorem head. Reuse existing exact consumers; do not build another conditional
receiver.

## 2026-08-14 source audit result

Mythos independently confirmed the local type audit:
`ProlatePair` does not express the prolate eigenfunction equation or the
lowest-two-even-mode selection.  The first honest source object is therefore
an external source-locked actual-mode predicate over the unchanged production
type, followed by existence/selection and the published Lemma 7.2 estimate.
There is no sound Aristotle task until the intended mode is policed by the
statement itself.

The limit-side denominator target has been narrowed further by
`E_star_explicitCCMLimitH_pos`: it is strictly positive for every `u >= 1`.
The missing floor is now a transport obligation from the actual prolate
approximation, not a missing positivity fact about the limiting packet.

A raw polynomial `PairIndex` schedule is only arithmetic plumbing.  It must
not be relabelled as a production `CentralIndex` path before the nonzero
selected-transform and actual-mode chain is proved.

## 2026-08-14 object lock

The external production predicate is now kernel checked as
`IsActualProlateModePair`; production `ProlatePair` was not changed.  The
permanent `looseProlatePairPlant_not_actual` theorem demonstrates that every
old record field can hold while the new source meaning fails.

The active source theorem has consequently narrowed to existence and
degree-`0/4` selection of a pair satisfying this predicate.  After that, the
published Lemma 7.2 estimate is the next supplier.  The predicate itself is a
contract, not existence and not G3 closure.

## Validators

Direct Lean, target build, full build at node close, `q3_check`, forbidden-token
scan, public axiom audit, strict Spine, RouteB status, and inventory/semantic
freshness. External review is requested only if the source theorem cannot be
resolved locally.

## 2026-08-14 constructor-capability audit

The statement boundary now also requires real-valued modes and interior
`C^2` regularity.  A current-tree audit found no ready constructor behind that
boundary.  Mathlib's implemented self-adjoint diagonalization is finite-
dimensional; compact self-adjoint spectral theory is explicitly a TODO.

The repository's deepest constructive alternative is a normalized mode-four
Jacobi recurrence row plus ordinary-Legendre algebra.  It still lacks the
Ferrers-series convergence through two derivatives, ODE and endpoint flux,
nontrivial regular solution, zero-count/order selection, and the corresponding
mode-zero construction.  Thus the current stop is
`ACTUAL_CCM_PROLATE_PAIR_CONSTRUCTOR_AND_LEMMA72_RATE_MISSING`, not another
receiver theorem and not an Aristotle-ready leaf.

The parallel G1 stop is
`LITERAL_CCM_QUANTITATIVE_SIMPLE_EVEN_GROUND_AND_TRACKING_MISSING`.  The full
input/output contract is preserved in
`GOAL058_G1_G3_CURRENT_PROBLEM_IO_LEDGER_2026-08-14.md`.

## 2026-08-14 mode-four Ferrers constructor progress

The narrower coefficient route is no longer stopped at convergence or the
interior differential equation.  Four kernel-checked files now prove:

- the exact ordinary-Legendre ODE, the sharp unit-interval bound, and interior
  first/second derivative majorants;
- absolute and polynomially weighted summability of the matched coefficient
  row, uniform convergence, and closed-window continuity;
- legal twice-termwise differentiation and interior `C2` regularity;
- absolutely summable three-band reindexing from the source recurrence to the
  exact prolate ODE, including the exceptional zero row.

The public constructor
`exists_mode4MatchedNormalizedProlateFerrersRow_of_root` now turns an exact
matching root into a nonzero normalized mode-four Ferrers function satisfying
that ODE.  Direct Lean, target build, and full build pass; its public axiom
audit is exactly `[propext, Classical.choice, Quot.sound]`.

This is a real source supplier, not G3 closure.  It remains conditional on a
matching root, and it does not yet prove endpoint realization, scaling to the
physical window, third-even/degree-four zero-count selection, the mode-zero
companion, the restricted finite-Fourier eigenrelations, CCM Lemma 7.2, or the
denominator floor.  The narrowed stop is
`MODE4_FERRERS_ODE_PROVED_MODE0_SELECTION_FOURIER_AND_LEMMA72_MISSING`.

## 2026-08-14 Sturm nodal-interval comparison

The Proshka-repaired compact-interior leaf is now kernel checked as
`exists_mode4Ferrers_zero_between_of_lt_Lambda_on_nodal_interval`.  For two
accepted regular mode-four Ferrers solutions with the same `mProject` and `K`,
`LambdaLo < LambdaHi`, and one zero-free nodal interval of the lower solution,
the higher solution has an interior zero.  The proof uses the exact weighted
Wronskian derivative, the actual first/second derivative interfaces, and the
previously proved simplicity of interior zeros.  Direct Lean, the 7773-job
target build, `q3_check`, and the 7817-job full build pass; the public axiom
surface is exactly `[propext, Classical.choice, Quot.sound]`.

The authorized Aristotle request was not sent because the exact leaf was
proved locally.  This closes only the bounded comparison kernel.  Compact
zero-set finiteness/consecutive-pair extraction, source-faithful index-4
selection, the mode-zero companion, physical scaling, finite-Fourier
identification, CCM Lemma 7.2, and the denominator floor remain open.  The
narrowed stop is
`MODE4_STURM_NODAL_COMPARISON_PROVED_COMPACT_ZERO_FINITE_SELECTION_MODE0_FOURIER_AND_LEMMA72_MISSING`.

## 2026-08-14 compact zero selection

The compact-selection layer is now kernel checked in
`D0Mode4FerrersCompactZeroSelection.lean`.  Simplicity of every interior zero
is converted into discreteness by `HasDerivAt.eventually_ne`; closedness and
compactness of the restricted zero set then give finiteness.  A finite-set
minimum selects the first zero to the right of a supplied endpoint.  This
discharges the separate nodal-interval binder and proves
`exists_mode4Ferrers_zero_between_of_lt_Lambda_between_lower_zeros`: between
any two distinct interior zeros of the lower-parameter accepted solution, the
higher-parameter solution has an interior zero.

Direct Lean, the 7774-job target build, the 7817-job full build, `q3_check`,
forbidden-token and claim scans pass.  Both public declarations have axiom surface exactly
`[propext, Classical.choice, Quot.sound]`.  This closes the compact zero-set
and consecutive-pair layer only.  It does not count all zeros, identify the
ordered degree-four mode, prove matching-root existence, construct mode zero,
or supply the physical/Fourier/Lemma 7.2 chain.  The narrowed stop is
`MODE4_UNRESTRICTED_STURM_COMPARISON_PROVED_INDEX4_MODE0_FOURIER_AND_LEMMA72_MISSING`.

## 2026-08-14 mode-four physical scaling

The source-pinned rescaling `x = u / sqrt(mProject)` is now kernel checked in
`D0Mode4FerrersPhysicalProlateScaling.lean`.  The scaled Ferrers series is
`C2` on `(-sqrt(mProject),sqrt(mProject))`; its declared scaled first and
second series are proved to be the actual derivatives.  The exact physical
equation is

```text
-(m-u^2) h''(u) + 2u h'(u) + (2*pi*sqrt(m)*u)^2 h(u)
  = (Lambda + mode4JacobiG m) h(u).
```

The root-conditioned wrapper
`exists_mode4MatchedNormalizedPhysicalProlateRow_of_root` preserves the
existing normalized coefficient row and exposes the physical ODE.  This is a
real scale bridge, not root existence or mode selection.  The remaining
mode-four wall is the classical regular `psi4` coefficient/minimal-tail
crosswalk and ordered index identification; mode zero, finite Fourier, Lemma
7.2 and the denominator floor remain open.  The narrowed stop is
`MODE4_PHYSICAL_SCALE_PROVED_SOURCE_PSI4_CROSSWALK_MODE0_FOURIER_AND_LEMMA72_MISSING`.

## 2026-08-14 parallel G1 exact Gram checker

The literal complex P59 trial-line complement floor is now fixed and its
finite-cell certificate soundness is kernel checked in
`CCMProposition59ComplexTrialComplementFloor.lean`.  An exact equality

```text
Q (K-aI) Q - beta Q = R^* R,  beta > 0
```

implies the required positive floor for the unchanged source CCM matrix, row,
and Rayleigh value.  A permanent exact `Fin 3` all-ones collapse plant proves
the source-shaped rank-two commutator while rejecting every positive floor and
every positive-floor Gram certificate.

This closes only the checker and permanently kills the commutator/beta-only
shortcut.  It does not construct `R`, `beta`, a finite-head certificate, a
uniform tail reduction, or a cofinal schedule.  The narrowed G1 stop is
`G1_LITERAL_COMPLEMENT_FLOOR_GRAM_CHECKER_PROVED_COFINAL_LITERAL_CCM_ARITHMETIC_AND_UNIFORM_TAIL_FLOOR_MISSING`.

## 2026-08-14 degree-four DLMF coefficient/root crosswalk

The normalization mismatch in the coefficient route is now resolved and
kernel checked.  For DLMF degree `n = 4`, order `m = 0`, reindexing by
`q = k + 2` gives weight `1/(4q+1)` but raw total `1/9`, not `1`.
Multiplication of the row by `3` preserves the homogeneous recurrence and
produces the exact unit normalization consumed by the current canonical-tail
theorem.

The new public theorem

```text
mode4DLMF3084_3085_degreeFour_coefficients_force_root
```

proves that a supplied literal reindexed 30.8.4 row with raw 30.8.5 sum
`1/9` forces the exact current
`mode4RootFunction mProject K Lambda = 0`.  It proves nonzero coefficient
zero, finite-left `mode4LeftPair` identification, canonical minimal-tail
transport, and the boundary matching equation; the root is not a binder.
Direct Lean passes and the public axiom surface is exactly
`[propext, Classical.choice, Quot.sound]`.

The remaining source wall is consequently smaller:

```text
CLASSICAL_INDEXED_PSI4_SUPPLIES_REINDEXED_DLMF_3084_3085_ROW_AND_FUNCTION_IDENTITY
```

That theorem must construct or extract the actual indexed classical `psi_4`
coefficient row and its Ferrers-series identity.  It must not merely place
the recurrence, index, root, or function identity into a new structure.  Mode
zero, the restricted finite-Fourier pair, CCM Lemma 7.2, the denominator
floor, and the coupled schedule remain open; G1 is unchanged.

## 2026-08-14 actual-mode regular packet consequence

The exact source predicate now discharges every separate regularity binder
needed by the existing production Muntz receiver.  In
`ProlateActualModeMuntzRegularity.lean`, the restricted nonzero
finite-Fourier eigenrelations rewrite each compactly supported mode as the
window indicator of a globally Lipschitz finite-Fourier action.  This proves
measurability and positive-half Lipschitz regularity, hence the complete
Muntz regularity package for the unchanged `prolateCombination`.

The same file proves two source consequences which were previously left at
the data boundary:

- `0 < P.normalizingDenominator` from the positive source integrals;
- `prolateCombination P != 0` from the exact Sturm selectors: the degree-four
  mode has an interior zero while the degree-zero mode has none.
- `∫ x, ‖prolateCombination P x‖^2 = 1` from the stored unit mode
  normalizations and the source orthogonality, with all integral operations
  justified by the derived measurability and `MemLp` facts.

Direct Lean, target build, full build, and `q3_check` pass; all five public theorem heads
have axiom surface exactly `[propext, Classical.choice, Quot.sound]`.  This
does not construct `P`, prove the Lemma 7.2 rate, establish `E_star` `MemLp`,
prove the selected projection nonzero or its quantitative denominator floor,
or choose a cofinal schedule.  The stop remains
`ACTUAL_MODE_EXISTENCE_LEMMA72_ESTAR_FLOOR_AND_SCHEDULE_MISSING`; G1 remains
open independently.

## 2026-08-14 actual-mode `E_star` carrier consequence

The production `MemLp` carrier is now a theorem consequence rather than an
independent source binder.  On `I_m`, `lambda_m = sqrt(m)` and
`u >= 1 / sqrt(m)`, so compact support at `[-lambda_m,lambda_m]` kills every
positive-integer summand with `n > m`.  The existing exact
`WindowFiniteSupport` crosswalk therefore rewrites `E_star` to the fixed
finite sum over `1 <= n <= m`.

`D0PstarActualProlateEStarMemLp.lean` proves that this finite sum is measurable
and uniformly bounded on the finite multiplicative-measure window, then
exports

```text
prolateCombination_E_star_memLp_of_actualModes
```

for the unchanged production objects.  Direct Lean, the 7761-job target
build, and the 7817-job full build pass; the public axiom surface is exactly
`[propext, Classical.choice, Quot.sound]`.

This does not prove that the projected trial is nonzero.  Exact unit `L2`
mass of the time-side packet cannot prevent cancellation of its sampled
`E_star` values.  The next load-bearing supplier is still the actual indexed
pair plus the uniform CCM Lemma 7.2 estimate, which transports the strictly
positive limiting `E_star` packet to a positive central overlap and then to a
projected denominator floor.  The narrowed G3 stop is
`ACTUAL_MODE_EXISTENCE_AND_LEMMA72_CENTRAL_MASS_FLOOR_SCHEDULE_MISSING`; G1 is
unchanged.

## 2026-08-14 `Lambda <= 20` oddity and resolution

During the indexed-source audit, the hard domain hypothesis
`Lambda <= 20` in the mode-four root/tail backend initially looked
incompatible with the cofinal physical scale
`c = 2*pi*mProject` and the crosswalk
`chi_4(c) = Lambda + c^2`.  The two plausible readings were a fatal shifted
spectral-parameter mismatch or a valid fixed-index upper bound.

The discriminator is the pinned Bonami--Karoui source
`docs/routeB_bus/litreview/pdfs/1405.3676.pdf`, physical page 5, equation (8):

```text
n(n+1) <= chi_n(c) <= n(n+1) + c^2.
```

At `n = 4`, this gives exactly `chi_4(c) - c^2 <= 20`.  Therefore the current
`Lambda <= 20` domain is source-compatible and is not a route kill.  The
remaining wall is still construction/selection of the indexed source row and
the separate Lemma 7.2 rate; no existence, G3, G1, promotion, or RH claim is
created by this unit check.

## 2026-08-14 exact Schur root order and simplicity

The exact continued-fraction backend now has the missing spectral-parameter
order facts.  `mode4RightTailLimit` is monotone in `Lambda` on the full
pole-free domain.  Consequently, when `Lambda_1 <= Lambda_2`, the exact
Hermitian Schur matrix at `Lambda_1` minus the matrix at `Lambda_2` dominates
`(Lambda_2 - Lambda_1) I` in positive-semidefinite order.  This is a theorem
about the actual infinite-tail correction, not a finite truncation or an
assumed eigenvalue monotonicity.

At every supplied exact matching root, consecutive finite-left continuants
cannot vanish together.  The `(K-1)` principal minor is therefore invertible,
and rank-nullity proves that the kernel of the literal Hermitian Schur matrix
has dimension exactly one.  Thus every exact root crossing is nullity-simple;
kernel multiplicity is no longer a source binder.

Direct Lean and target builds pass, and every new public theorem has axiom
surface exactly `[propext, Classical.choice, Quot.sound]`.  This still does
not construct an endpoint or a root, prove the inertia count at an endpoint,
formalize the monotone inertia jump, identify the third even root with indexed
`psi_4`, construct mode zero, or supply the finite-Fourier/Lemma 7.2/floor
chain.  The narrowed root-selection wall is
`SCHUR_PARAMETER_DROP_AND_SIMPLE_ROOT_PROVED_ENDPOINT_INERTIA_LADDER_AND_INDEX4_SELECTION_MISSING`.

## 2026-08-14 exact one-direction inertia jump

The missing internal inertia-ladder mechanism is now kernel checked.  The
general real-Hermitian theorem
`hermitian_negativeCount_add_nullity_le_of_strict_drop` proves

```text
A - B - delta I >= 0, delta > 0
  -> negativeCount(A) + nullity(A) <= negativeCount(B).
```

Its proof uses the spectral subspace of `A` with eigenvalues at most zero and
the Sylvester subspace argument; the proof architecture is explicitly
attributed to the registered Apache-2.0 `zeta23` base at pin `3635e74`.
The literal mode-four specialization proves that every strict increase of
`Lambda` grows the negative index by at least the starting nullity.  Combining
this with the already proved one-dimensional root kernel gives
`negativeCount(A(Lambda)) + 1 <= negativeCount(A(LambdaHi))` after every exact
matching root.

Direct Lean passes and the public axiom surface is exactly
`[propext, Classical.choice, Quot.sound]`.  This closes the crossing direction
and one-step inertia jump, not the source endpoint counts, existence and
ordering of three even crossings, or the identification of the third crossing
with indexed `psi_4`.  Mode zero, restricted finite Fourier, CCM Lemma 7.2,
the denominator floor, G1, G3, Route B promotion, and RH remain open.  The
narrowed stop is
`ROOT_QUADRATIC_AND_ONE_DIRECTION_INERTIA_JUMP_PROVED_SOURCE_ENDPOINT_COUNTS_AND_INDEX4_SELECTION_MISSING`.

## 2026-08-14 exact Schur-root inertia labels

The one-direction jump now composes into a strict root-label theorem.  For any
two supplied exact matching roots in the pole-free source domain,

```text
Lambda_1 < Lambda_2
  <-> negativeCount(A(Lambda_1)) < negativeCount(A(Lambda_2)).
```

Therefore two exact roots have the same Hermitian negative-eigenvalue count if
and only if they are equal.  The Schur negative count is now an injective,
order-preserving label on the exact roots; no continuous eigenvalue numbering
or new source binder is used.

This still does not construct a root, provide an endpoint count, prove that
three even crossings exist, or identify the count-two root with the classical
indexed `psi_4`.  The remaining source wall is
`SCHUR_ROOT_INERTIA_LABEL_INJECTIVE_SOURCE_ROOT_EXISTENCE_ENDPOINT_COUNTS_AND_INDEX4_IDENTIFICATION_MISSING`.
Mode zero, restricted finite Fourier, CCM Lemma 7.2, the denominator floor,
G1, G3, Route B promotion, and RH remain open.
