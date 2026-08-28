---
TASK_ID: GOAL058_R1_SAME_GROUND_FAMILY_VITALI_OBJECT_LOCK_PREFLIGHT
PHASE: 0 — addendum, anchor repair
MODE: PAPER_AND_SOURCE_READ_ONLY
BODY: Linux-Claude
DATE: 2026-08-28
SUPERSEDES: 9ff604bd section 3 (the point-anchor gauge)
DISCRIMINATOR: PASS with a gauge change
RESULT_CODE: POINT_ANCHOR_BLOCKED_L2_GAUGE_SUPPLIES_TIGHTNESS_FREE
LEAN_EDIT: false
NUMERICS: DIAGNOSTIC_ONLY, declared
RH_CLAIM: false
CLOSES:
  - R1_B_GROUND_FAMILY_NONZERO_TIGHTNESS
OPENS: []
---

# The point anchor is blocked; an `L^2` gauge supplies tightness with no rate

## 1. What the anchor actually is

Computed from the source. `proposition59PoleKernel L k` is `dslope` of
`2 sin(z L/2)` at `p_k = 2 pi k/L`. At `z = 0`:

- for `k != 0`, the numerator is `2 sin 0 - 2 sin(k pi) = 0` and the denominator
  `0 - p_k` is nonzero, so `kappa_k(0) = 0`;
- for `k = 0`, `p_0 = 0` and `dslope` at the point is the derivative,
  `kappa_0(0) = L cos 0 = L`.

Therefore, **exactly**,

    T(v)(0) = sum_k v_k kappa_k(0) = L * v_0.                            (1)

Confirmed numerically at `L = 3.7, 9.2`: every entry vanishes except `k = 0`,
which equals `L`.

So `GROUND_TRANSFORM_ANCHOR_NONVANISHING` is **equivalent** to

    xi_k(0) != 0,   the ground vector's centre coordinate.

## 2. The catalogue does not supply it, and the obvious route is forbidden

Asked the shelf. What is supplied for the ground vector is parity, simplicity and
a spectral gap: `H2a_SimpleEvenGround_FromPenaltyCoercivity`,
`simpleEvenGround_of_sector_order`,
`weighted_projective_defect_mul_gap_le_rayleigh_excess`. **Evenness does not force
a nonzero centre coordinate** — an even vector may have `xi_0 = 0`.

The route that does exist is quantitative and dangerous. From
`selectedFerrersTrackedGroundVector_spec` the projective defect satisfies
`1 - |<xi, q>|^2 <= ||r||^2/beta^2`. Writing `xi = c q + w`, `w ⊥ q`,
`||w||^2 <= ratio`, and using the banked inverse-log floor on the **trial** centre
coefficient `|q_0| >= c_0/L`,

    |xi_0| >= |c| |q_0| - |w_0| >= sqrt(1 - ratio) * c_0/L - sqrt(ratio),

which is positive only for `ratio <~ c_0^2/L^2`. That is a bound on
`selectedFerrersTrackedGroundResidualFloorRatio`, i.e. residual energy over the
squared complement floor — the tracking quantity the corridor could never bound.
Using it would import the dead object under a new name, which verdict `bc51e294`
forbids explicitly.

**So the point anchor at `z = 0` is blocked, and my Phase-0 section 3 gauge is
withdrawn.**

## 3. The repair: gauge by an `L^2` norm on one fixed compact

Fix once, before any `k`, a compact `K_0` in the centered critical strip with
nonempty interior. Define

    hat F_k(z) := T(xi_k)(z) / || T(xi_k) ||_{L^2(K_0)}.                 (2)

Three facts, none of them a rate.

**(a) The gauge is well defined.** `xi_k != 0` and the `kappa_k` are linearly
independent, so `T(xi_k)` is entire and not identically zero; an entire function
not identically zero has positive `L^2` norm on a set with interior. This is
qualitative and holds at every cell, with no floor and no ratio.

**(b) Real zeros survive.** `hat F_k` is a **positive scalar** multiple of
`T(xi_k)`, hence of `F_k`, so
`ZerosRealOn Set.univ (hat F_k)` follows from the banked
`selectedFerrersTrackedGroundTransform_realZeros_..._of_sectorFloors` without
touching its forbidden second conjunct. `SlotS2` already admits an arbitrary
nonzero scalar, so nothing downstream is disturbed.

**(c) Tightness is immediate.** By construction `|| hat F_k ||_{L^2(K_0)} = 1` for
every `k`. Locally uniform convergence on `K_0` implies `L^2(K_0)` convergence, so
any Montel limit has `L^2(K_0)` norm `1`, hence is not identically zero on `K_0`;
the strip is preconnected (`isPreconnected_centeredCriticalStrip`), so by the
identity theorem the limit is not identically zero near **any** point of the
strip. That is exactly `limitNonzero`.

So `R1_B` is discharged by the choice of gauge, with no analytic input.

## 4. What this does to `R1_A`, and it is a real reduction

For holomorphic `f` and `K` compact with `K` contained in the interior of `K_0`
at distance `r`, the mean value property and Cauchy-Schwarz give

    sup_K |f| <= (1/(r sqrt(pi))) * || f ||_{L^2(K_0)},

with a constant depending only on `K` and `K_0`. Applied to (2), **uniformly in
`k`**,

    sup_K | hat F_k | <= 1/(r sqrt(pi))   for every K compactly inside K_0.   (3)

So local boundedness on compacts strictly inside the gauge set is **free**. What
remains of `R1_A` is not "prove a bound" but "propagate a bound": extend (3) from
a neighbourhood of `K_0` to the whole centered critical strip.

That is precisely the shape Phase 1 was authorized to acquire from primary
literature, and the named source families fit it: Cartwright class for entire
functions of exponential type with **real zeros** — which is exactly what section
3(b) supplies for our family — de Branges spaces, and Herglotz compactness for
logarithmic derivatives. The family's exponential type is `L_k/2` and grows with
the cell, so a naive Phragmen-Lindelof step is not enough; the real-zero
structure is what a Cartwright-type argument would consume.

## 5. Status

    R1_0  locked (9ff604bd), with section 3 of that report superseded here.
    R1_B  discharged by the L^2 gauge, no rate used.
    R1_A  reduced to: propagate (3) from a fixed compact to the strip, using
          real-zero / Cartwright / de Branges structure. This is Phase 1.
    R1_C  unchanged.

The two sector floors remain definitional inputs of the family; nothing here
touches them.

## 6. Declaration

The only computation is (1), checked symbolically from the `dslope` definition and
confirmed numerically at two values of `L`; it is an identity, not an estimate.
Facts (a), (b), (c) and (3) are standard complex analysis with explicit constants.
No Lean, no new object: `hat F_k` is a positive scalar multiple of a banked
family.
