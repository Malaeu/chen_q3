# Mythos verdict — Goal 058 actual source closure

Date: 2026-08-14
Browser chat: `https://claude.ai/chat/3bbe2272-8bc5-49ba-ab80-d723e24f3a8d`
Request tip: `453dc7e7`
Context SHA-256: `46b12aea6be1746f83bbae876795a256527b73d9dee38cd6f25a2a77d4b672cc`

This file preserves the completed Mythos browser verdict.  Editorial headings
and repository addresses were added locally; the mathematical decision and
the ordered action list below are faithful to the browser response.

## Operative verdict

```text
PRIMARY: G3_ACTUAL_MODE_CONSTRUCTOR_IS_THE_FIRST_SOURCE_THEOREM
ARISTOTLE: NO_SOUND_ARISTOTLE_TASK_AT_THIS_BOUNDARY
```

## First hidden object gap

The production `ProlatePair` surface does not contain a prolate
eigenfunction equation or a lowest-even-mode selection predicate.  Its stored
facts are parity, support, normalization, integrals, and the two centre
identities `I = chi * h(0)`.  Those fields alone do not distinguish the actual
degree `0/4` prolate modes from arbitrary even bump functions with compatible
centre scalars.

Therefore the phrase "actual normalized degree 0/4 prolate modes" is not yet
expressed by the Lean type.  A bounded constructor search would be unsound:
it could satisfy `ProlatePair` with non-modes and report success.

The first honest G3 source object should be an external, source-locked
predicate over the unchanged production type, for example
`IsActualProlateModePair : ProlatePair -> Prop`.  It must record the literal
operator realization and the selection of the two lowest even modes.  The
production type must not be replaced by a parallel strengthened family.

## G3 source decomposition

1. Formalize existence and selection of the actual modes from the literal
   Sturm--Liouville / compact-operator realization.
2. Formalize the published CCM Lemma 7.2 estimate
   `sup_[−lambda,lambda] |h_lambda - h| <= C * lambda^-2` against the already
   kernel-checked `explicitCCMLimitH`; the pinned statement is in
   `q3.lean.aristotle/literature/zotero/H8ULBMAL/fulltext.md:1299-1308`.
3. Derive the central floor and coupled schedule only after those suppliers
   exist.  A raw `PairIndex` schedule is not by itself a production
   `CentralIndex` path, because the latter also needs the nonzero selected
   transform condition.

The browser response proposed the polynomial raw schedule
`sigma(j) = (j+2, (j+2)^2)`, for which `N/log m -> infinity` is elementary.
Local adjudication narrows this claim: the arithmetic schedule is available,
but production schedule closure still depends on the actual-mode and
central-nonzero source chain.

## G1 source decomposition

The G1 wall is mathematically different.  The published CCM argument does not
prove a literal quantitative even-sector gap.  The all-ones `3 x 3`
falsifier correctly kills the commutator-only shortcut.

The named invention target remains
`ccmBeta_dividedDifference_complement_floor`: quantitative definiteness of the
literal divided-difference beta form on the complement of the trial line,
with constants derived from the prime sums.  Per-cell interval certificates
may calibrate or falsify that theorem, but do not discharge its cofinal
quantifier.

## Aristotle decision

`NO_SOUND_ARISTOTLE_TASK_AT_THIS_BOUNDARY` for three precise reasons:

- actual-mode existence/selection and the semiclassical Lemma 7.2 comparison
  are not bounded proof search;
- the current type does not police the intended source object, so an honest
  success predicate cannot yet be stated;
- the remaining bounded fragments are local definitions, plants, or small
  arithmetic lemmas rather than a theorem-sized external task.

## Exact next action returned by Mythos

1. Define the external source-locked actual-mode predicate over production
   `ProlatePair`, leaving production types untouched.
2. Compile a permanent `LoosePairPlant`: a non-mode term satisfying the
   current weak record surface, and prove it does not satisfy the actual-mode
   predicate.
3. Compile the raw polynomial `PairIndex` schedule and its cofinal arithmetic,
   without calling it a production `CentralIndex` supplier.
4. Open CCM Lemma 7.2 as a named analysis project with milestones: operator
   realization, semiclassical comparison, and a uniform constant.
5. Keep G1 parallel under the named
   `ccmBeta_dividedDifference_complement_floor` invention target.

## Boundary

No G1/G3 close, no Aristotle submission, no Route B promotion, and no RH
claim follows from this verdict.
