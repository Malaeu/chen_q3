---
TASK_ID: GOAL058_R1_LITERAL_GROUND_LOCAL_SPECTRAL_COUNT_PREFLIGHT
MODE: PAPER_SOURCE_AND_PRIMARY_LITERATURE_READ_ONLY plus declared numeric verification
BODY: Linux-Claude
DATE: 2026-08-28
RESPONDS_TO: afd27ddf
DISCRIMINATOR: HOLD
RESULT_CODE: R1_ZERO_DIVISOR_EXACT_BUT_LOCAL_FINITE_SPECTRUM_UNCONTROLLED
LEAN_EDIT: false
NUMERICS: DIAGNOSTIC_NEVER_A_PROOF, declared
RH_CLAIM: false
CLOSES:
  - SIGN_INDEPENDENT_ZERO_COUNT_ASSUMPTION
OPENS:
  - SELECTED_GROUND_VECTOR_COEFFICIENT_SIGN_PATTERN
---

# The local zero count is decided by one thing: the sign pattern of the ground vector

## 1. Repairs accepted

My "the sine lattice forces dense literal zeros" is withdrawn. The included
lattice points are **removable evaluation points**: at the pole labelled `j` the
transform equals an explicit nonzero scalar times the coefficient `xi_j`, so the
point is a zero **iff** `xi_j = 0`. That is the same identity I derived earlier as
`T(v)(p_j) = (-1)^j L v_j`, and it cuts against my own alarm.

Exterior lattice escape is accepted: on the schedule `m_k = N_k = k+2` the nearest
exterior zero sits at `2 pi (N_k+1)/L_k -> infinity`, so it leaves every fixed
compact.

So the zero divisor on a fixed compact consists of the **off-lattice** zeros
alone, and those are the finite perturbed spectrum of the verdict's `R2` object.

## 2. The secular form, and the one thing it depends on

From the verdict's determinant ratio, the off-lattice zeros are the zeros of

    S(s) = sum_j xi_j/(j - s),

a finite sum with poles at the lattice indices in the carrier. Its local zero
count on a fixed interval is **entirely governed by the sign pattern of `xi`**,
and the two regimes are as far apart as they can be.

**If all `xi_j` have one sign**, then between consecutive poles
`d/ds [ xi_j/(j-s) ] = xi_j/(j-s)^2` has that same sign, so `S` is strictly
monotone across each gap and runs from `-infinity` to `+infinity`. Exactly one
zero per gap: **strict interlacing**, and the local count equals the number of
lattice gaps in the interval, which on a fixed compact of the `z`-strip is
`~ L_k |K|/(2 pi) -> infinity`. R1 dies by the `cos(n z)` mechanism.

**If the signs vary**, monotonicity fails and gaps may hold no zero at all.

Measured on `N = 12`, twelve lattice gaps in `[-6,6]`:

    all positive, Gaussian profile   : 12 zeros  (one per gap, interlacing)
    all positive, equal weights      : 12 zeros
    alternating signs (-1)^j         :  0 zeros
    random signs                     :  3 zeros

So the answer is not "a bit smaller"; it is the difference between full
interlacing and none.

## 3. Consequence for my own alarm

The profile I used to raise the alarm — a centred Gaussian-Hermite row — is
**all positive**. I measured the worst case and reported its growth as if it were
generic. The alarm stands as a possibility and is withdrawn as a prediction.

## 4. The gate, and a link the corridor should notice

    SELECTED_GROUND_VECTOR_COEFFICIENT_SIGN_PATTERN:
    does the literal selected ground eigenvector have coefficients of one sign?

If **yes**, R1 dies. If **no**, the local count may be bounded and R1 survives the
`cos(n z)` kill.

The link. One-signed bottom eigenvectors are what Perron-Frobenius structure
produces, and Perron structure for our matrix is exactly the question of whether
the off-diagonal Loewner entries can be given a single sign by a diagonal gauge.
That is the **Ricci/Doob sign gate** of `3f4c23eb`, which is `OPEN`: my parity
argument for its failure was refuted, and no replacement was proved.

So the two questions are the same family, with the polarity reversed: a sign gate
**PASS** would make the matrix Perron-like, hence the ground vector one-signed,
hence R1 dead. A sign gate **FAIL** is what R1 needs. I record this because the
corridor previously treated the sign gate as a side diagnostic worth deferring;
under R1 it is load-bearing and its favourable outcome is the opposite of what was
assumed.

## 5. Guards

- The lattice is not counted as zeros inside the carrier (verdict stop rule 1).
- Interlacing is asserted **only** under a one-sign hypothesis, which is exactly
  the residue-sign condition the stop rule demands; no interlacing is inferred
  otherwise (stop rule 2).
- Model-row numerics are not promoted to the literal family (stop rule 3): section
  2's table is a statement about the secular function's dependence on signs, not
  about the literal ground vector, and section 3 withdraws my earlier promotion.

## 6. Next load-bearing gap

    SELECTED_GROUND_VECTOR_COEFFICIENT_SIGN_PATTERN

a property of one banked eigenvector, decidable from the source or from a spectral
theorem about the literal CCM matrix. It now controls R1 outright.
