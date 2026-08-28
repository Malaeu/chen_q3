---
TASK_ID: GOAL058_R1_KREIN_NEGATIVE_SQUARE_GATE_WELL_POSEDNESS
MODE: DEFINITION_READ_ON_DISK_PLUS_CATALOGUE
BODY: Linux-Claude
DATE: 2026-08-28
RESPONDS_TO: own preflight 91e40850 section 4
DISCRIMINATOR: FAIL
RESULT_CODE: THE_GATE_IS_NOT_A_MISSING_THEOREM_THE_CONSTRUCTION_DOES_NOT_DETERMINE_THE_QUANTITY
LEAN_EDIT: false
NUMERICS: none
RH_CLAIM: false
CLOSES:
  - KREIN_NEGATIVE_SQUARE_COUNT_OF_THE_LITERAL_GROUND_ROW (withdrawn as ill-posed)
OPENS: []
MERGES_INTO:
  - G3_UNIQUE_CURRENT_REGULAR_SOLUTION_TO_CLASSICAL_PSF_ZEROCOUNT_SOURCE_GAP
---

# The Krein gate is not a theorem we lack; it is a question our object does not answer

## 1. What I asked in `91e40850`

    KREIN_NEGATIVE_SQUARE_COUNT_OF_THE_LITERAL_GROUND_ROW:
    is the number of sign changes of the literal selected ground row, restricted
    to any central window of O(log m) modes, bounded uniformly in k?

I called it "a statement about one banked eigenvector". I read the summary of the
object, not its definition. The definition says otherwise.

## 2. What the object actually is

`selectedFerrersTrackedGroundVector`
(`G6N1SelectedFerrersTrackedGroundTransform.lean:97`) is

    Classical.choose (Classical.choose_spec (gtt_ground_extraction P k beta (hfloor k)))

so everything knowable about it is in the extraction spec
(`gtt_ground_extraction`, line 50). That spec has exactly two conjuncts:

    complexHermitianGroundGapAtLeast (sourceCCMFiniteMatrix (index k)) epsilon beta xi0
    1 - normSq (star xi0 dot row) <= (star residual dot residual).re / beta^2

and `complexHermitianGroundGapAtLeast`
(`CCMProposition59ComplexTrialComplementSpectral.lean:27`) unfolds to four
conjuncts: unit norm, the eigenvector equation, `epsilon` as the bottom Rayleigh,
and a gap `beta` on the orthogonal complement.

**All six conditions are spectral. None mentions the sign pattern.**

## 3. Three reasons the question does not attach, in order of decisiveness

**(a) The vector is complex.** Its type is
`CCMModeFinite (index k).N -> ℂ`. "Number of sign changes" is undefined for a
complex vector. It needs a reality statement plus a phase lock, and neither is in
the spec.

**(b) The spec is invariant under everything that moves signs.** A ground vector is
determined only up to a unit complex scalar, and `Classical.choose` fixes no
representative. Multiplying by `-1` satisfies every conjunct and reverses every
sign; multiplying by `i` destroys reality outright.

**(c) The overlap bound cannot repair it.** The second conjunct places `xi0` near
the explicit trial row in overlap. **Overlap is one global inner product; a
variation count is pointwise.** An `l^2` perturbation of size `eps` flips the sign
of every coordinate whose magnitude is below `eps`, at no cost in overlap. So
closeness to an explicit row bounds no variation count. This is the same
correction-15 boundary in a new coordinate: a trial property is not a ground
property.

## 4. A named false friend

`IsRealEigenvector` (`SimpleEvenGroundSectorCriterion.lean:12`) reads

    x != 0 and A x = (mu : ℂ) • x,   mu : ℝ

It asserts the **eigenvalue** is real. It says nothing about the entries of `x`.
The name invites exactly the misreading that would have let this pass, and I record
it as a false friend rather than as a supplier.

## 5. W9: this does not open a new input

The missing object is a nodal / variation count on the current class. The project
already carries that open input under its own name: the boundary
`G3_UNIQUE_CURRENT_REGULAR_SOLUTION_TO_CLASSICAL_PSF_ZEROCOUNT_SOURCE_GAP`, and
`D0Mode4FerrersRegularEvenProlateSolutionUniqueness.lean:13` disclaims in its own
header that it does not "prove an interior zero count, supply a Sturm oscillation
theorem". Opening `KREIN_NEGATIVE_SQUARE_COUNT_OF_THE_LITERAL_GROUND_ROW` as a new
input would be a rename of something already open. It is merged, not added, and my
`OPENS` list here is empty.

## 6. Consequence for R1

R1 does not fail for want of a theorem to acquire. It fails because **the object as
constructed does not determine the quantity the gate needs**. Making it answerable
means strengthening `gtt_ground_extraction` itself — producing a real, phase-locked
ground vector with a controlled variation count — which is new construction, not
acquisition, and is the same nodal-count supplier that has been open since G3.

## 7. One unfavourable reading, recorded and not used as a premise

`relay, not verified from a primary source in this session:` in the classical
Gantmacher-Krein theory of oscillation matrices, the eigenvector at the `j`-th
eigenvalue carries exactly `j - 1` sign changes, so the **bottom** eigenvector
carries the maximal count `n - 1`. If the source matrix had that structure, the
count would be `2N` and unbounded in `k`. I do not assert the matrix is
oscillatory, and section 6 does not depend on this. It is recorded because it is
the only classical structure that would settle the count, and it points away from
us.

## 8. Ledger

    CLOSES:  KREIN_NEGATIVE_SQUARE_COUNT_OF_THE_LITERAL_GROUND_ROW, withdrawn
             as ill-posed against the current construction
    OPENS:   nothing
    MERGES:  into the standing G3 nodal-count / Sturm oscillation supplier gap
    UNCHANGED: the banked target-preservation result c0b44cbb; the per-cell
             zero-set transfer stays valid and rate-free
