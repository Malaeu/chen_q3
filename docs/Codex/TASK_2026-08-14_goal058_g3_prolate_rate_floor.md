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
