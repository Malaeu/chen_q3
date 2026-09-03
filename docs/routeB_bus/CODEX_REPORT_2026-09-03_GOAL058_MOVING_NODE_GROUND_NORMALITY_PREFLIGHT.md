# Goal 058 moving-node ground-normality preflight

```yaml
STATUS: SOURCE_CHECK_COMPLETE
DATE: 2026-09-03
SOURCE_BASE_COMMIT: 7e4c60d19cb6da956af7a8bf278edc1a69906e39
GOAL: REALZERO_GROUND_DIAGONAL_TO_XI
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
MOVING_NODE_STATUS: UNRESOLVED_DIRECT_GROUND_NORMALITY
SCOPED_KILL: KILL_SCALAR_ENVELOPE_NORMALITY
RELLICH_SHORTCUT: KILL_TRY_RELLICH_COFINAL_AS_G1_SUPPLIER
LEAN_CHANGED: false
NUMERICS_RUN: false
```

## Decision

The moving-node route remains an unresolved candidate weakening of the existing
compact-decay contract, but it is not yet a proof.  Its noncircular form must
replace

```text
A_n * sup_{z in K} kernel_n(z) * sqrt(r_n) -> 0
```

on every compact `K` by the pair

```text
for every compact K subset strip, there exists M_K such that
  eventually for every z in K, ‖F_n(z)‖ <= M_K
A_n * sqrt(L_n) * sqrt(r_n) -> 0
```

where

```text
k_n = phi(n), the same cofinal tail index used by F_n and hfloorAt(n)
A_n = ‖centeredXi 0 / rawFplus_(k_n) 0‖
r_n = selectedFerrersTrackedGroundResidualFloorRatio P beta k_n
L_n = logLength(index k_n).
```

The first line is eventual direct compact-local boundedness of the tracked
ground family.  Since every finite-head function is entire and therefore
bounded on a compact, a finite-head absorption wrapper upgrades it to the
all-index bound required by the existing Montel theorem.  It must not be
replaced silently by boundedness of the scalar tracking envelope.  The second
line supplies convergence only at the moving real lattice.
For every subsequence, Montel must produce a further locally-uniformly
convergent subsequence.  Density identifies that subsubsequence limit with
`centeredXi` on a real interval, and the analytic identity theorem identifies
it on the centered critical strip.  Only the universal statement that every
subsequence has a subsubsequence with this same limit permits the standard
unique-cluster argument concluding convergence of the original sequence.

## Checked exact facts

1. `proposition59PoleKernel_sum_at_lattice` samples exactly one coefficient at
   a lattice point.  After the raw `L^(-1/2)` factor, the value is
   `sqrt L * (-1)^j * v_j`.
2. The production source-ordered transform uses the reflected node
   `z = -proposition59Pole L (ccmModeFinite N i)`.
3. Before cofinal reindexing the production schedule has `m = N = k + 2`.
   Consequently the mesh `2*pi/log m` tends to zero while the covered radius
   `2*pi*N/log m` tends to infinity.  A strict cofinal reindex preserves both
   facts.
4. The tracked ground family is entire and has real zeros once the existing
   sector-floor hypotheses are supplied.
5. Generic Montel machinery already exists in
   `Q3.Proofs.RouteB.MontelCenteredCriticalStrip`.
6. The available identity theorem is
   `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`.
7. Existing `SelectedLocallyBoundedOnCenteredCriticalStrip` is about the trial
   family `selectedFamily`, not
   `selectedFerrersTrackedGroundTransformAt`.

## Minimum consumer-sufficient contract

Let `F n` be the tracked-ground transform on the already constructed cofinal
tail and let `G n` be the corresponding `centeredPstar` trial family.

```text
GROUND_HOLOMORPHIC:
  forall n, Differentiable C (F n)                         [already supplied]

GROUND_REAL_ZEROS:
  forall n, ZerosRealOn univ (F n)                        [already supplied]

TRIAL_LIMIT:
  TendstoLocallyUniformlyOn G centeredXi atTop strip      [already supplied]

GROUND_COMPACT_BOUNDED:
  forall compact K subset strip,
    exists n0 M, forall n >= n0 and z in K, ‖F n z‖ <= M  [missing analytic supplier]

FINITE_HEAD_ABSORPTION:
  continuity of each F n on compact K upgrades the eventual bound
  to the all-n bound required by Montel                       [Lean-ready]

LATTICE_RATE:
  A_n * sqrt(L_n) * sqrt(r_n) -> 0                        [missing analytic supplier]

POLE_DENSITY:
  for every real x in a fixed nontrivial interval,
    exists lattice nodes x_k -> x on the cofinal schedule [missing arithmetic wrapper]

MOVING_NODE_IDENTIFICATION:
  for every subsequence s, Montel supplies a subsubsequence t;
  the moving lattice for s o t identifies its limit with
  centeredXi on the interval and hence on strip;
  universal unique-cluster convergence then gives F -> centeredXi
                                                            [missing Lean composition]
```

The arithmetic density, finite sample-evaluation wrapper, and final Montel
composition are expected to be Lean work after the two analytic suppliers are
fixed.  They must not be confused with source evidence for those suppliers.

An initially proposed sufficient route to `GROUND_COMPACT_BOUNDED` was a
bounded scalar tracking envelope

```text
A_n * kernel_n(z) * sqrt(r_n) = O_K(1).
```

That route is not retained as the new hypothesis.  The exact whole-lattice
kernel formula has exponential growth in `L * |Im z|`.  A bound at one height
`sigma1` appears to force exponential decay of the tail scalar prefactor, which then
gives compact decay at every smaller height `sigma0 < sigma1`.  Thus this
particular sufficient condition likely repackages the old compact-decay wall.
Only a direct ground-family normality supplier, not obtained from that scalar
envelope, could preserve the proposed weakening.  The scalar-envelope branch
is therefore killed; the direct-normality branch is not.

## Rellich preflight

`TRY_RELLICH_COFINAL` is not a supplier for production G1.  The production
matrix is `ccmWeilMatFinite mProject N`, with natural-valued `mProject`, a
prime sum changing with `mProject`, and a dimension changing with `N`.
No source-faithful continuous analytic family agreeing with these matrices is
registered.  Suzuki's infinite operator result supplies neither that finite
analytic family nor cofinal even-sector dominance.  Simplicity alone gives
`even or odd`; the required even branch needs a strict sector-order theorem.

## Shelf result

The complete registered shelf and live Lean tree were queried for moving
lattice sampling, tracked-ground compact boundedness, Montel, and the exact
residual/floor ratio.  No exact ground-local-boundedness supplier or lattice-rate
supplier was found.  The search did find reusable generic Montel machinery and
the already known gap/residual inequalities.  Those do not establish either
missing analytic statement.

## Exact next decision

The front should remain on the moving-node route only if independent review
confirms all of the following:

1. the moving-node identification implication is logically sufficient;
2. direct ground-family normality plus the lattice scalar rate is a weaker
   source contract than the old scalar compact-decay hypothesis, without
   presupposing the desired functional convergence as an input;
3. neither condition silently assumes convergence of the tracked ground family;
4. at least one source-faithful attack on ground normality or the lattice rate
   exists that is not merely the old compact-decay target under a new name.
