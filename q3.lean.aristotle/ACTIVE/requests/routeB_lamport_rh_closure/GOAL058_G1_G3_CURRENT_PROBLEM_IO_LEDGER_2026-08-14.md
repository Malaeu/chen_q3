# Goal 058 G1/G3 current problem I/O ledger

Date: 2026-08-14

Lane: `CHALLENGER / NOT_RH`

Verdict: `MODE4_FERRERS_ODE_PASS / G1_OPEN / G3_OPEN`

## Owner-language summary

The route now has the exact finite CCM matrix, the exact prolate trial, the
parity split, the P59 entire-function bridge, and a positive limiting prolate
anchor. It still lacks two load-bearing theorems:

1. **G3:** finish the actual source prolate modes around the now-constructed
   mode-four Ferrers ODE supplier, then prove the paper's quantitative rate
   and a denominator floor for their trial family;
2. **G1:** prove that the literal finite CCM ground is simple/even with a
   quantitative gap, and that the same source trial approaches it on one
   cofinal schedule.

Neither missing theorem is a wrapper or a numerical cell. Both are new
uniform mathematics.

## G3 — actual prolate family and rate

### Exact inputs

- bandwidth `lambda > 0`, eventually `lambda = sqrt m` on the selected source
  family;
- the source Sturm--Liouville degrees `0` and `4` on
  `[-lambda,lambda]`, with real-valued interior-`C^2` representatives;
- zero-flux endpoint realization, simplicity, parity, and exact zero-count
  selection;
- positive-integral normalization and the exact plus-phase restricted
  finite-Fourier eigenrelations `h0 <-> chi0`, `h4 <-> chi2`;
- the unchanged production carrier `ProlatePair`.

The exact Lean statement boundary is already fixed by
`Q3.RouteB.D0Pstar.IsActualProlateModePair`. A smallest honest constructor
head would have the shape

```lean
theorem exists_actualProlateModePair
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ P : ProlatePair,
      P.pw.lambda = lambda ∧ IsActualProlateModePair P
```

This head is a target specification, not a theorem currently present on disk.

### Required outputs

1. an actual `ProlatePair` satisfying that predicate for every required
   bandwidth;
2. the source-locked CCM Lemma 7.2 comparison between `prolateCombination P`
   and `explicitCCMLimitH`, with the uniform `O(lambda^-2)` error on the paper
   window;
3. transport through `E_star` and finite projection;
4. an eventually positive quantitative lower bound for the normalization
   denominator on one precommitted cofinal schedule.

Those outputs would supply the prolate rate/floor side of G3. They would not
by themselves prove G1, Route B, or RH.

### What is already kernel checked

- `ProlateSourceRegularity.lean`: exact finite-Fourier kernel, Lipschitz
  regularity, and transfer through a supplied nonzero eigenrelation;
- `ProlateSourceCommutation.lean`: exact differential-expression / finite-
  Fourier intertwining;
- `ProlateSourceEigenTransport.lean`: a supplied differential eigenmode is
  transported into the same eigenspace;
- `ProlateFiniteFourierNonvanishing.lean`: the finite-Fourier action of a
  supplied nontrivial interior mode is nonzero somewhere;
- `D0Mode4JacobiMatchedNormalizedCoefficientRow.lean`: a normalized exact
  mode-four recurrence row from a certified root;
- `D0Mode4OrdinaryLegendreIntervalBound.lean`: the exact Legendre ODE,
  `|P_n| <= 1` on `[-1,1]`, and interior first/second derivative bounds;
- `D0Mode4FerrersCoefficientAbsoluteSummability.lean`: absolute and every
  polynomially weighted coefficient summability, uniform convergence, and
  closed-window continuity of the even Ferrers series;
- `D0Mode4FerrersInteriorRegularity.lean`: legal twice-termwise
  differentiation and `ContDiffOn R 2` on `(-1,1)`;
- `D0Mode4FerrersProlateDifferentialEquation.lean`: legal reindexing of the
  three absolutely summable Legendre bands, the exact prolate ODE, and a
  root-conditioned normalized mode-four Ferrers constructor.

This closes the former `recurrence row -> convergent C2 Ferrers function ->
exact prolate ODE` gap for mode four.  It does not identify that function as
the third even/degree-four PSWF, and it does not construct the mode-zero
companion or a production `ProlatePair`.

### Exact missing library layer

Pinned Mathlib's `Analysis/InnerProductSpace/Spectrum.lean` implements the
self-adjoint spectral theorem only in finite dimension and lists compact
self-adjoint spectral theory as a `TODO`. `IsCompactOperator` exists, but no
ready infinite-dimensional compact-self-adjoint eigenbasis constructor was
found. The project likewise has no formal singular Sturm--Liouville
self-adjoint realization or oscillation/index-selection theorem.

The narrower coefficient route has now discharged Ferrers/Legendre
convergence through two derivatives, the interior prolate ODE, and
nontriviality of the normalized row conditional on an exact matching root.
The remaining source layer is: unconditional certified root brackets on the
required family; endpoint realization/flux; exact scaling to
`[-lambda,lambda]`; zero-count/order selection showing the third even mode;
the corresponding mode-zero construction; and the restricted plus-phase
finite-Fourier eigenrelations.  Only after those can the unchanged
`ProlatePair` be constructed and CCM Lemma 7.2 consumed.

Narrowed source stop:

```text
MODE4_FERRERS_ODE_PROVED_MODE0_SELECTION_FOURIER_AND_LEMMA72_MISSING
```

Stop code:

```text
ACTUAL_CCM_PROLATE_PAIR_CONSTRUCTOR_AND_LEMMA72_RATE_MISSING
```

## G1 — literal CCM simple-even ground and cofinal tracking

### Exact inputs

- literal matrix family `ccmWeilMatFinite m N` on `CCMModeFinite N`;
- its exact reflection symmetry and even/odd sector decomposition;
- exact structured off-diagonal formula and rank-two commutator;
- the unchanged unit source row `sourceCCMComplexRow m N` produced from the
  same prolate trial;
- one precommitted cofinal schedule `(m_j,N_j)`.

### Required outputs

For all sufficiently large `j`, prove on that same schedule:

- a unique even ground vector `xi0_j`;
- a positive quantitative even-sector gap lower envelope
  `0 < D(j) <= Delta_even(j)`;
- an even Rayleigh-excess or residual upper envelope `A(j)` for the exact
  source row;
- an odd-mass upper envelope `W(j)` for that same row;
- decay strong enough that `W(j) + A(j)/D(j) -> 0` (or the corresponding
  squared-residual form).

The already checked parity-sector projective estimate then turns those inputs
into convergence of the source trial to the finite ground. P59 can transport
that ground convergence to the analytic zero-set object.

### Killed shortcuts

1. **Commutator alone.** The exact Lean plant
   `/tmp/Goal058CommutatorGapCollapse.lean` satisfies the source-shaped
   rank-two commutator while its ground kernel has dimension two. Therefore
   structure/commutation does not imply simplicity or a positive gap.
2. **Beta-only determinant factor.** Already for the source-shaped
   centrosymmetric `3 x 3` family, the even/odd collision depends on the
   diagonal arithmetic; the current beta identities do not control it.

A clean sufficient decomposition is an even-sector Krylov determinant
nonvanishing theorem plus strict sector ordering
`minSpec(T_even) < minSpec(T_odd)`. For the full spectrum one would need both
sector Krylov determinants and cross-sector separation. None of these literal
CCM arithmetic statements is currently on disk, and nonvanishing alone would
still not give the quantitative all-large gap envelope required by G1.

Stop code:

```text
LITERAL_CCM_QUANTITATIVE_SIMPLE_EVEN_GROUND_AND_TRACKING_MISSING
```

## External adjudication

Both living reviewers reached the same boundary:

- Mythos: `G3_ACTUAL_MODE_CONSTRUCTOR_IS_THE_FIRST_SOURCE_THEOREM`;
- Proshka: `NO_SOUND_ARISTOTLE_TASK_AT_THIS_BOUNDARY`, naming
  `ActualCCMProlatePairConstructor` for G3 and
  `LiteralCCMQuantitativeComplementFloor` for G1.

No Aristotle request was needed for the new mode-four step: the bounded
Ferrers convergence, differentiation, legal band reindexing, and ODE theorem
were proved locally and kernel checked.  The next remaining selection and
Fourier/source-rate wall is still not a bounded cloud-prover leaf.

## Nonclaims

```text
NO_G1
NO_G3
NO_ROUTE_B_PROMOTION
NO_RH
```
