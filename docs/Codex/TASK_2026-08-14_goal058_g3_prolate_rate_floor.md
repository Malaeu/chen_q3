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

## 2026-08-14 post-inertia joint source verdict

Mythos proposed source endpoint counts on architectural placeholder objects.
After exact attachment-based source-lock restoration, Proshka rejected that
task: the placeholder names are absent, `20 + ε` violates the literal
`ΛUpper ≤ 20` receiver, and the proposed `0/3` program does not match the
current moving-endpoint `2/3` supplier contract.

The smallest honest G3 source object is now named
`MODE4_CLASSICAL_EVEN_SPECTRUM_TO_LITERAL_SCHUR_INERTIA_CROSSWALK`. It must
independently identify the negative count of
`mode4HermitianSchurMatrix mProject Λ K` with the classical even
Sturm--Liouville spectral counting function and prove the exact finite-split
offset. Bonami--Karoui separators become endpoint-count suppliers only after
that crosswalk. Aristotle was not authorized.

The active stop is
`CLASSICAL_EVEN_SPECTRUM_TO_LITERAL_SCHUR_INERTIA_CROSSWALK_MISSING`.
This does not close matching-root/indexed-`psi4` existence, mode zero,
restricted finite Fourier, Lemma 7.2, denominator floor, G1, G3, Route B, or
RH.

## 2026-08-14 actual finite Schur provenance and tail positivity

The terminal-zero backward-tail approximation is now connected to a literal
finite Hermitian Jacobi truncation.  The exact Schur complement onto the
retained block was first proved under explicit recursive nonzero pivots and
accepted by Proshka.  The follow-up leaf
`D0Mode4BackwardTailFiniteTailPosDef.lean` then proves, under the production
separation inequality and `Lambda <= 20`, that the actual eliminated finite
tail block is `Matrix.PosDef` for every depth, including the empty `d=0`
carrier.

The same follow-up discharges every recursive elimination pivot internally
and exports the exact public Schur identity without the predecessor's private
pivot predicate.  Its coercive estimate is

```text
mode4JacobiLower G K * x_0^2 + (G/12) * sum_i x_i^2
  <= star x dot (A x).
```

All direct Lean, target-build, full-build, `q3_check`, forbidden-token,
axiom-profile, and strict-startup gates passed.  Four kernel-checked scratch
plants separately reject Hermitian-implies-PosDef, removal of separation,
removal of `Lambda <= 20`, and tail reversal.  Proshka accepted the exact
Lean/report hashes and corrected one filename-only transport typo without
changing the mathematical verdict.  The accepted proof/report commit is
`16d603c5`.

The independent Aristotle attempt for the predecessor finite-Schur contract
later completed, but its alternative implementation was not consumed by this
proof or its review.

This is still a finite-cell result.  It proves no block-inertia equality,
negative count, limit stabilization, zero offset, or endpoint count `2/3`.
The next bounded finite-Jacobi leaf is
`G3_MODE4_FINITE_BLOCK_INERTIA_ADDITIVITY`: prove the exact congruence/inertia
identity for the same block orientation using the new `PosDef` tail and exact
Schur crosswalk.  The classical-spectrum-to-literal-Schur count crosswalk,
indexed mode selection, mode zero, restricted finite Fourier, CCM Lemma 7.2,
denominator floor, G1, G3, Route B promotion, and RH all remain open.

## 2026-08-14 literal DLMF even finite matrix and exact similarity

The finite source object previously marked `NOT_READY` is now kernel checked
in `D0Mode4DLMFEvenFiniteMatrix.lean`.  The file defines the literal even
`m = 0` DLMF 30.16.1 matrix in source order and project units
`G = gamma^2`, `Lambda = lambda`, with the shift already equal to
`-Lambda I`.

The positive recursive diagonal scale proves the exact similarity equation

```text
A_DLMF * D = D * H_forward,
```

and an explicit `Fin.rev` submatrix identity proves that `H_forward` is exactly
the existing `mode4HermitianLeftContinuantMatrix` in its reversed orientation.
The public package
`mode4DLMFEvenFiniteMatrix_similar_hermitianLeftContinuantMatrix` exposes both
identities and strict positivity of every scale entry. Direct Lean, target
build, full build, `q3_check`, forbidden-token scan, and the public axiom audit
all pass; the public axiom surface is exactly
`[propext, Classical.choice, Quot.sound]`.

This closes the literal matrix/permutation/positive-diagonal-conjugator leaf,
not the source count.  The bounded finite-tail PosDef, Schur identity,
block-inertia additivity, stability, and finite-to-literal count transport are
already present.  The next source object must now materialize the classical
even spheroidal spectral carrier and prove ordered finite-eigenvalue
convergence strongly enough to supply the exact endpoint negative counts
`2/3` and the index-four identification.  Those values may not be inserted as
binders.

The narrowed G3 stop is
`DLMF_EVEN_FINITE_MATRIX_AND_EXACT_SIMILARITY_PROVED_ORDERED_EIGENVALUE_LIMIT_ENDPOINT_COUNTS_2_3_AND_INDEX4_IDENTIFICATION_MISSING`.
G1 remains independently open at the even-head/shift/cofinal full-complement
floor.  No G1, G3, Route B, or RH promotion follows from this node.

## 2026-08-14 full finite DLMF spectrum crosswalk

The remaining finite-carrier orientation gap is now kernel checked in
`D0Mode4DLMFFullFiniteSpectrumCrosswalk.lean`.  The exact equivalence from the
actual Schur carrier `Fin K ⊕ Fin d` to the forward source carrier
`Fin (K + d)` reverses only the retained block and leaves the tail in forward
order.  Under this equivalence the complete actual finite Jacobi truncation is
exactly the forward Hermitian DLMF matrix.

Consequently the actual truncation, the forward Hermitian matrix, and the
literal nonsymmetric DLMF 30.16.1 matrix have the same characteristic
polynomial on the full finite carrier.  The node also proves Hermiticity of the
forward matrix, the literal scalar shift
`H(G,Lambda) = H(G,0) - Lambda I`, and materializes a zero-based ascending
finite eigenvalue family with proved monotonicity.

Direct Lean, the 7756-job target build, the 7817-job full build, `q3_check`,
forbidden-token/whitespace checks, and public axiom audit all pass.  Every
public theorem uses only `[propext, Classical.choice, Quot.sound]`.

This closes the finite matrix, orientation, shift, characteristic-polynomial,
and finite-ordering seams.  It does not supply the analytic DLMF 30.16.3
same-index limit, a classical even spheroidal spectral carrier, the exact
endpoint counts `2/3`, or the degree-four identification.  The next object is
therefore genuinely source-analytic rather than another finite algebra
adapter; the required counts may not be inserted as binders.

The narrowed G3 stop is
`DLMF_FULL_FINITE_SPECTRUM_CROSSWALK_PROVED_ORDERED_FINITE_TO_CLASSICAL_LIMIT_ENDPOINT_COUNTS_2_3_AND_INDEX4_IDENTIFICATION_MISSING`.
G1 remains independently open at the even-head/shift/cofinal full-complement
floor.  No G1, G3, Route B, or RH promotion follows from this node.

## 2026-08-14 joint analytic source-wall review and G1 C1 leaf

The attachment-based Mythos and Proshka verdicts are now durable in the Goal
058 request directory.  Proshka rejected the proposed G3 finite-limit carrier
as circular: defining the classical spectrum by the finite limit cannot prove
that this limit is the differential Sturm--Liouville spectrum in DLMF 30.16.3.
The G3 stop therefore remains the same-index analytic limit, exact endpoint
counts `2/3`, and degree-four identification above.  Aristotle is not ready
for that source theorem.

For G1, Proshka selected the one bounded noncircular local leaf.  The new
kernel-checked theorem
`sourceWeilOddTailInverseWeightedCorrection_quadraticForm_le` proves

```text
min mu 1 * Re <R^* C^-1 R x, x> <= 2 * ||R x||^2
```

for the actual source odd-tail graph operator and actual inverse.  It consumes
the literal graph coercivity and exact inverse equation and uses no finite
section or scalar inverse surrogate.  Direct Lean, named target build,
`q3_check`, source scans, and the axiom audit pass; the public axiom surface is
exactly `[propext, Classical.choice, Quot.sound]`.

This closes only the C1 correction budget.  The corrected even-head sign,
exact row evenness (or an explicit odd-contamination budget), cofinal shift
connector, and full complex trial-complement floor remain missing.  The
narrowed G1 stop is
`G1_ODD_TAIL_CORRECTION_BOUND_PROVED_CORRECTED_EVEN_HEAD_ROW_EVENNESS_AND_COFINAL_FULL_COMPLEMENT_FLOOR_MISSING`.
No G1, G3, Route B, or RH promotion follows.

## 2026-08-14 production-schedule odd-head crosswalk

The historical `m = 13` restriction on the exact corrected odd-head matrix
receiver is now removed. `sourceWeilOddSynthesis` and
`sourceWeilOddFormPullback` are kernel checked for an arbitrary production
`PairIndex`, and
`sourceWeilOddTargetFloorSchurComplement_isPositive_iff_ccm_corrected_energy`
identifies the actual odd Schur sign on every cell with the literal corrected
CCM quadratic energy at the analytic tail cutoff.

This closes only the fixed-cell adapter seam. It does not prove that the
corrected energy is nonnegative or uniformly positive. The even leg, exact
source-row reflection evenness or an explicit odd-contamination rate, and the
fixed-shift/cofinal connector remain missing. The narrowed G1 stop is

```text
G1_ODD_HEAD_CROSSWALK_GENERIC_CORRECTED_SIGN_EVEN_LEG_ROW_REFLECTION_DEFECT_AND_COFINAL_SHIFT_MISSING
```

The G3 DLMF same-index analytic-limit wall is unchanged. No G1, G3, Route B,
or RH promotion follows.

## 2026-08-14 finite-limit carrier and literal Schur count bridge

The bounded H1--H6 program is now kernel checked in three new Route B files.
The literal bordered Hermitian DLMF family supplies exact Cauchy interlacing
and a uniform Gershgorin lower bound.  Its fixed-index `iInf` therefore defines
an internal finite-limit carrier with unconditional convergence and monotone
ordering.  This carrier is used only for inertia bookkeeping: no theorem in
this node identifies it with an independently constructed differential
Sturm--Liouville or PSWF spectrum.

The same node proves pointwise equality between the literal finite spectral
count and the actual finite Jacobi negative count.  A finite-head plus one
next-index tail separator then gives eventual count stabilization, which is
composed with the already accepted finite-to-literal Schur transport.  The
finite split offset is exactly zero.  Tail separation, `Lambda <= 20`, literal
Schur determinant nonsingularity, and the carrier window remain distinct
inputs; endpoint counts `2/3` are not inserted as assumptions or conclusions.

An exact `3 x 3` positive-definiteness certificate additionally proves
`mode4ClassicalEvenEigenvalue G p < 20` for `p < 3` and `G > 0`.  Thus the
left half of the upper endpoint window is available at `LambdaUpper = 20`.
The right inequality `20 < carrier_3` and determinant nonsingularity are not
proved.

The remaining honest G3 source object is a source-backed two-sided fixed-index
separator package on the production cofinal schedule, for example
`mode4SemiclassicalWindowSeparators`, supplying

```text
carrier_0, carrier_1 < LambdaLower < carrier_2
carrier_0, carrier_1, carrier_2 < LambdaUpper < carrier_3,
LambdaUpper <= 20,
```

together with, or followed by, literal Schur determinant nonsingularity at
both endpoints.  A theorem taking these desired inequalities as arbitrary
binders would be another receiver and would not close the source wall.

The active G3 stop is
`FINITE_LIMIT_CARRIER_AND_SCHUR_COUNT_BRIDGE_PROVED_SEMICLASSICAL_WINDOW_SEPARATORS_AND_ENDPOINT_NONSINGULARITY_MISSING`.
G1 remains independently open at the cofinal even-head floor and shift
connector for the full complex trial complement.  The prepared Proshka packet
requests adjudication of this narrow carrier boundary before any further
source import.  No G1, G3, Route B, or RH promotion follows.

## 2026-08-14 Proshka acceptance and DLMF strict-order source packet

The exact H1--H6 packet was delivered to the existing Goal 058 Proshka phase
as byte-verified UTF-8 text after the raw-link transport failed closed.
Proshka returned `H1_H6_BOUNDARY_VERDICT: ACCEPT`: the internal `iInf` carrier
is legal for finite inertia bookkeeping, and H5's finite-head plus one
next-index tail condition really prevents finite spectral pollution without a
hidden global count.  The verdict does not identify the carrier with a
differential PSWF spectrum.

The source audit selected a smaller remaining window package than the earlier
explicit semiclassical proposal.  DLMF 30.16.3 identifies the same fixed-index
finite limit with the independently defined differential eigenvalue
`lambda_(2p)^0(G)`, while DLMF 30.3.1 strictly orders those eigenvalues.  Once
that source identity is materialized, midpoint endpoints between carriers
`1/2` and `2/3` give the two strict windows by ordered-field arithmetic; the
already proved `carrier_2 < 20` makes the upper midpoint admissible.  The
Bonami--Karoui elliptic-integral separator remains a valid stronger alternate
source but is no longer the minimal window supplier.

The read-only packet
`GOAL058_G3_DLMF_3016_303_STRICT_ORDER_AND_LITERAL_ROOT_AVOIDANCE_SOURCE_PACKET_2026-08-14.md`
locks the exact DLMF selector and unit dictionary and records
`LITERAL_ROOT_CROSSWALK_MISSING`.  The current tree nearly closes the algebraic
half (`det Schur = 0` reduces to `mode4RootFunction = 0` through a positive
factor), but it has no converse equivalence between that project root and an
independently indexed finite-limit carrier value.  The existing classical
coefficient-row theorem is only one-way and consumes the row it would need to
construct.

The active G3 stop is now

```text
G3_DLMF_STRICT_ORDER_SOURCE_LOCKED_LITERAL_ROOT_CROSSWALK_MISSING
```

The exact next Lean head remains `NOT_READY`, and Aristotle remains
`NOT_AUTHORIZED`.  G1 remains independently open at the cofinal even-head
floor, row-reflection/contamination control, and shift connector for the full
complex complement.  No endpoint count in Lean, G1, G3, Route B promotion, or
RH claim follows.

## 2026-08-14 DLMF 30.3.5 literal-root ruling

Proshka narrowed the root wall from an unknown mathematical crosswalk to a
known source mechanism that is not yet formalized. Official DLMF 30.3.5 gives
the exact even-spectrum solution set of the two-sided continued-fraction
equation. The remaining task is not another conditional receiver: it is the
independent source object
`mode4DLMF3035EvenCharacteristicEquation` and the paper-backed theorem
`mode4DLMF30163_3035_evenCharacteristicSolutions`.

The source contract must preserve three load-bearing locks:

```text
project Lambda = DLMF lambda
differential chi = Lambda + G
DLMF splitDegree = 2 * (K - 1)
```

It must separately prove that the DLMF recessive infinite right fraction is
the project's contraction-selected square-summable `mode4RightTailLimit`.
Defining the source equation by `mode4RootFunction = 0`, replacing the right
branch by a terminal-zero finite tail, or using endpoint counts `2/3` is
circular and forbidden.

The active G3 stop is
`G3_DLMF3035_SOURCE_THEOREM_NOT_LEAN_MATERIALIZED`. Aristotle is not
authorized until the source theorem exists; only then is the local
root-function-to-Schur-determinant adapter a bounded Aristotle candidate.
G1 remains independently open. No Route B or RH promotion follows.
