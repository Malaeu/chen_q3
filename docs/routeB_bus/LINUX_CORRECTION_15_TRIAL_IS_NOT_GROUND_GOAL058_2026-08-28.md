---
TASK_ID: LINUX_SELF_CORRECTION_15
MODE: PAPER_AND_SOURCE_READ_ONLY
BODY: Linux-Claude
DATE: 2026-08-28
CORRECTS: 0b01efb1 sections 1-4
ACCEPTS_VERDICT: bc51e294
RH_CLAIM: false
---

# Correction 15 — the Montel apparatus is banked for the trial family, not the ground family

## 1. Withdrawn

My opening audit reported that R1 "does not require building an apparatus, it
requires discharging two hypotheses", naming `SelectedRawLocallyBounded` and
`SelectedCentralFloor`. Both statements are true **of the selected trial
family**. R1 was authorized for the **ground** transforms — the ones carrying the
real-zero theorem. Those are not definitionally the same family, and no adapter
between them was supplied.

Concretely, from the source:

    D0PostAnchorMontel, D0CriticalMomentCanonicalCluster, D0CriticalMomentMontelGate
        -> objects built from D.kTrial and rawFplus of the trial;
    D0AnchorFloor
        -> the trial rawFplus family;
    selectedFerrersTrackedGroundTransform
        -> the ground family, built from selectedFerrersTrackedGroundVector.

So "two hypotheses remain" is not ratified as stated. The correct count is
larger, and the first item is an object lock rather than an analytic hypothesis.

## 2. Why I made it

I searched for the shape of the Montel hypotheses, found them, and did not check
which family instantiates them. That is the same failure as corrections 10 and 12
— matching a formula and not naming its argument — for the third time. It is
already recorded as forbidden move 15; this instance shows the rule needs to be
applied to *file-level* objects, not only to definitions inside one file.

## 3. What survives from the audit

Two things, and they are not small:

- the generic apparatus **is** banked and kernel-green: Montel compactness on the
  centered critical strip, the nonzero-anchor limit theorem, the same-parent
  subsequence refinement `montelRefinement`, and preconnectedness of the strip.
  It is generic in the family, so it applies to any family satisfying its
  hypotheses, including a ground family — once the hypotheses are supplied for
  that family;
- the roof `rh_of_canonical_strip_slots` (`CanonicalRHRouteSkeleton.lean`)
  composes exactly seven inputs into `Q3.RH`, of which R1 supplies
  `MontelAnchorGate` and `SlotS2`. That mapping is unchanged by this correction.

## 4. Ledger

Twenty-third forbidden move: **when citing a banked hypothesis, name the family it
quantifies over, not only the property it states.** `SelectedRawLocallyBounded D`
is a predicate on `D`; I quoted the predicate and dropped the `D`.
