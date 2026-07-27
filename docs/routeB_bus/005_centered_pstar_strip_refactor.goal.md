# 005 — centered Pstar and strip-local roof

Owner directive: `2026-07-27`

Owner-sign:

```text
PROSHKA_VERDICT_S1_ANCHOR_2026-07-27.md
```

## Goal

1. Add the section-iii family verbatim:

```lean
def centeredPstarFamily
    (D : CoefficientFamily) (i : CentralIndex D) (z : ℂ) : ℂ :=
  (centeredXi 0 / rawFplus D i.1 0) * rawFplus D i.1 z
```

2. Bind `canonicalApproximation.Pstar` to `centeredPstarFamily`.
3. Apply Kill 7 to the canonical skeleton:
   - cluster holomorphy only on `centeredCriticalStrip`;
   - local uniform convergence only on `centeredCriticalStrip`;
   - local Hurwitz transfer on that strip;
   - export `rh_of_canonical_strip_slots`.
4. Preserve the old `rh_of_canonical_slots` name only as a compatibility
   wrapper; it must not restore a `Set.univ` convergence hypothesis.
5. Update `STATE.json` only after code, report, and validation are complete.

## Honesty

This is a conditional roof refactor.  It does not prove S1, the anchor floor,
the project slots, or RH.
