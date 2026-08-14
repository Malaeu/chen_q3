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
