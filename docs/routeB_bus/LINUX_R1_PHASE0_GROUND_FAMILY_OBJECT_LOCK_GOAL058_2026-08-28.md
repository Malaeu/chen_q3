---
TASK_ID: GOAL058_R1_SAME_GROUND_FAMILY_VITALI_OBJECT_LOCK_PREFLIGHT
PHASE: 0 — literal object and anchor lock
MODE: PAPER_AND_SOURCE_READ_ONLY
BODY: Linux-Claude
DATE: 2026-08-28
RESPONDS_TO: bc51e294
DISCRIMINATOR: PASS for the object lock, with a gauge repair
RESULT_CODE: GROUND_FAMILY_LOCKED_ANCHOR_AVAILABLE_AFTER_REGAUGE
LEAN_EDIT: false
NUMERICS: none
NEW_MATHEMATICAL_OBJECT: none — the proposed gauge is a scalar multiple of an existing family
RH_CLAIM: false
CLOSES:
  - R1_0_GROUND_FAMILY_OBJECT_LOCK
OPENS:
  - GROUND_TRANSFORM_ANCHOR_NONVANISHING
---

# Phase 0: the ground family, its gauge, and why the anchor needs a repair

## 1. The literal family

    F_k(z) = selectedFerrersTrackedGroundTransform P beta hfloor k z
           = scale_k * sourceOrderedCCMRawTransform L_k N_k xi_k z,

`G6N1SelectedFerrersTrackedGroundTransform.lean:168`, where

    xi_k    = selectedFerrersTrackedGroundVector P beta hfloor k,
    L_k     = logLength (index k),   N_k = (index k).N,
    scale_k = ( centeredXi 0 / rawFplus_k 0 ) * overlap_k          (line 154),
    overlap_k = star xi_k .-. selectedFerrersFiniteCCMRow P k       (line 134),

and `sourceOrderedCCMRawTransform L N q z = proposition59RawTransform L (Icc (-N) N)
(sourceOrderedCCMCoefficient N q) (-z)`.

**Schedule and carrier.** `index k = (selectedFerrersCofinalSourceData P).index k`,
the frozen selected schedule; carrier `CCMModeFinite N_k`.

**Floor inputs, both open and both named in the corridor already.**

- `hfloor`: `complexTrialComplementFloor (sourceCCMFiniteMatrix (index k)) (row k)
  (Rayleigh k) beta` for every `k` — this is `SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR`;
- `hoddFloor`: `beta0 * ||x||^2 <= Re <x, (M - a I) x>` for every reflection-odd
  `x` — this is `SELECTED_FERRERS_ODD_SECTOR_FLOOR`;
- `hratio`: `selectedFerrersTrackedGroundResidualFloorRatio P beta k < 1`.

The family is **defined** under `hfloor`, not merely estimated under it.

## 2. The real-zero theorem, on the same family

`selectedFerrersTrackedGroundTransform_realZeros_and_pointwiseTracking_of_sectorFloors`
(line 399, `#print axioms` at 666) gives, under the three floor inputs above,

    ZerosRealOn Set.univ (selectedFerrersTrackedGroundTransform P beta hfloor k)

together with a pointwise tracking bound. **The second conjunct is the forbidden
object** per `bc51e294`, and is not used anywhere below.

So `Theorem510RealZeroBridge` is instantiated for this literal family. That is the
whole point of choosing it.

## 3. The gauge, and the repair the anchor needs

The trial family is anchored exactly: `centeredPstarFamily D i z =
(centeredXi 0 / rawFplus D i 0) * rawFplus D i z`, so
`centeredPstarFamily_zero` (`D0CanonicalApproximation.lean:147`) gives
`centeredPstarFamily D i 0 = centeredXi 0` — a fixed nonzero value, the same for
every index. That is a textbook fixed compact-open witness.

The ground family does **not** inherit it. Its gauge divides by `rawFplus_k 0`,
which is the **trial's** value at the anchor, and multiplies by `overlap_k`.
Hence

    F_k(0) = ( centeredXi 0 / rawFplus_k 0 ) * overlap_k * T(xi_k)(0),

and equality with `centeredXi 0` would require
`overlap_k * T(xi_k)(0) = rawFplus_k 0`, which is not an identity: the graph
relation `d^{-1} xi - q = -C^{-1} r` with `d = <q, xi>` relates `T(xi)/d` to
`T(q)` **up to the residual term**, not exactly. Closing that gap with the
tracking bound is precisely what the verdict forbids.

**Repair, and it costs nothing.** Real-zeroness is invariant under multiplication
by a nonzero scalar, and `SlotS2` already permits an arbitrary nonzero `c`. So
re-gauge the family at the anchor:

    tilde F_k(z) := centeredXi 0 * T(xi_k)(z) / T(xi_k)(0),
    T := sourceOrderedCCMRawTransform L_k N_k.

Then, **by construction and with no estimate**,

    tilde F_k(0) = centeredXi 0   for every k,

a fixed nonzero value of a fixed compact-open continuous functional
(evaluation at `0`). And `ZerosRealOn Set.univ (tilde F_k)` follows from section 2
because `tilde F_k` is a nonzero scalar multiple of `F_k` wherever both are
defined. No new mathematical object is introduced: `tilde F_k` is
`(centeredXi 0 / (scale_k^{-1} F_k(0))) * F_k` written without the trial anchor.

The **only** new requirement is

    GROUND_TRANSFORM_ANCHOR_NONVANISHING:   T(xi_k)(0) != 0 for every k.

This is qualitative. It is not a rate, it does not mention the residual, the
graph resolvent or the arithmetic, and it is the exact analogue of what
`rawFplus_zero_ne` already supplies on the trial side.

## 4. Eta normalization audit

The verdict warns that eta normalization on a growing coefficient carrier is not
automatically a fixed compact-open functional. Confirmed and avoided: our gauge is
**not** eta. `eta` pairs against the all-ones vector on a carrier of growing
dimension, so the functional `v -> <eta, v>` changes with `k` and is not a fixed
continuous functional on any one function space. Evaluation at the fixed point
`z = 0` is a fixed functional on `H(strip)` with the compact-open topology, and
it is the one the repaired gauge uses.

## 5. The mandatory plant: a moving normalization escapes every compact

Take `v_k` supported at the single mode `n = N_k`, `||v_k||_2 = 1`. Its transform
is `T(v_k)(z) = kappa_{N_k}(z) = L_k sin(w)/(w - N_k pi)`, `w = z L_k/2`. On any
fixed compact `K` in the strip, `|w| = O(L_k)` while `N_k pi = m_k pi`, so

    sup_{z in K} |T(v_k)(z)| = O( L_k m_k^{sigma_K/2} / m_k ) -> 0.

The family is `l^2`-normalized at every `k`, yet converges to the zero function
locally uniformly. Montel would return a cluster whose limit is identically zero,
and `limitNonzero` would fail. So coefficient normalization alone is not
tightness, and the anchor of section 3 is doing real work.

## 6. Hard stop check

The verdict's hard stop fires only if **no** fixed point, fixed jet or
compact-tight normalization functional is source-ready. Section 3 supplies one
after a scalar re-gauge, subject to a single qualitative nonvanishing statement.
So the stop does not fire, and Phase 1 may proceed — but only once
`GROUND_TRANSFORM_ANCHOR_NONVANISHING` is either found in the catalogue or
adjudicated as the first theorem-sized node.

I did not audit that item in this pass and do not assert it. It is returned as the
exact missing statement, in the verdict's own required form.

## 7. Ledger

    CLOSES: R1_0_GROUND_FAMILY_OBJECT_LOCK
    OPENS:  GROUND_TRANSFORM_ANCHOR_NONVANISHING
    UNCHANGED: R1_A, R1_B (now reduced to the item above plus Phase 1), R1_C
    CARRIED: SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR,
             SELECTED_FERRERS_ODD_SECTOR_FLOOR — both are definitional inputs of
             the family, not merely estimates about it.
