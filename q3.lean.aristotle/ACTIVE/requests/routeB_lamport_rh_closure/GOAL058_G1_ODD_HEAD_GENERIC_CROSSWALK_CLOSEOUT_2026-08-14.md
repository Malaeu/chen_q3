# Goal 058 G1 — production-schedule odd-head crosswalk closeout

Date: 2026-08-14

Route state: `CHALLENGER / NOT_RH`

Node verdict: `PROVED`

Goal 058: `OPEN`

## Selected local leaf

The joint source-wall verdict split the surviving G1 route into C1/C2/C3.
After the C1 inverse-weighted correction bound, the next C1 adapter was the
historical `m = 13` restriction on the exact corrected odd-head CCM pullback.
The underlying source-Weil finite-form theorem was already generic in
`PairIndex`; only the normalized antisymmetric synthesis and matrix receiver
were fixed to one cell.

The knowledge and supplier preflights found the generic finite-form supplier

```text
sourceWeilSesquilinearForm_apply_ccmFiniteSynthesis
```

but the elaborated environment index was stale for two current modules, so the
supplier preflight correctly returned `INCOMPLETE`. Exact applicability was
therefore established only by direct Lean typechecking and the named build.

## Kernel-checked result

The existing pullback file now exports the generic declarations

```text
Q3.RouteB.D0Pstar.sourceWeilOddSynthesis
Q3.RouteB.D0Pstar.sourceWeilOddSynthesis_eq_normalized_mode_sum
Q3.RouteB.D0Pstar.sourceWeilOddFormPullback
```

for an arbitrary production `PairIndex`. The historical `m = 13`
declarations remain unchanged and available.

Modified file:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilOddFormPullback13.lean
SHA-256 92dc1f4ab185344b13aab59f54209cbcfa72200176612a860d0c9866c4dee2f6
```

The new generic receiver file is:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilOddTargetFloorSchurMatrixGeneric.lean
SHA-256 ef07940abb893692500374b790faaefb4395aa5b3e1b2ac73ab32b93d9ede30e
```

Its final public equivalence

```text
Q3.RouteB.D0Pstar.
  sourceWeilOddTargetFloorSchurComplement_isPositive_iff_ccm_corrected_energy
```

states, for every production cell, that positivity of the actual odd-tail
Schur complement at the registered floor is exactly nonnegativity of the
literal corrected finite CCM quadratic energy. The matrix uses the cell's
actual `i.m`, the analytic cutoff `sourceWeilOddTailCutoff i`, and the actual
inverse-weighted infinite-tail correction.

## Validation

Direct Lean passes for both files. The named target build passes with 7,822
jobs, the full build passes with 7,817 jobs, and `q3_check` passes for both
files. Whitespace and forbidden-token scans are clean. Every printed public declaration has exactly the standard
axiom surface

```text
[propext, Classical.choice, Quot.sound]
```

The only build warning is the pre-existing local-change warning for the
external `UnicodeBasic` dependency.

## Honest boundary

This node removes the fixed-`m = 13` adapter restriction. It does not prove
the corrected finite-head sign, a uniform lower bound, an even-tail or
even-head estimate, exact reflection-evenness of the production source row,
an explicit odd-contamination rate, a fixed-shift Rayleigh connector, or the
full complex trial-complement floor.

In particular, exact production-row evenness is not manufactured: the tree
retains the exact reflection-defect/odd-mass identities and their
approximation receivers. A clean parity split still needs exact evenness, or
the full theorem must carry a quantified odd-contamination budget.

The narrowed G1 stop is:

```text
G1_ODD_HEAD_CROSSWALK_GENERIC_CORRECTED_SIGN_EVEN_LEG_ROW_REFLECTION_DEFECT_AND_COFINAL_SHIFT_MISSING
```

The G3 stop is unchanged:

```text
DLMF_FULL_FINITE_SPECTRUM_CROSSWALK_PROVED_ORDERED_FINITE_TO_CLASSICAL_LIMIT_ENDPOINT_COUNTS_2_3_AND_INDEX4_IDENTIFICATION_MISSING
```

No G1, G3, Route B, or RH promotion follows from this node.
