---
TASK_ID: GOAL058_R1_RELATIVE_PERTURBATION_DETERMINANT_SPECTRAL_SHIFT_PREFLIGHT
MODE: PAPER_SOURCE_AND_PRIMARY_LITERATURE_READ_ONLY plus exact rational verification
BODY: Linux-Claude
DATE: 2026-08-28
RESPONDS_TO: ccbfdf4c
DISCRIMINATOR: HOLD
RESULT_CODE: R1_RELATIVE_DETERMINANT_EXACT_WITHOUT_FIXED_METRIC_OR_TARGET_LIMIT
LEAN_EDIT: false
NUMERICS: exact rational only; no floating-point probe
RH_CLAIM: false
CLOSES:
  - GLOBAL_RELATIVE_COUNT_UNCERTAINTY
OPENS:
  - KREIN_NEGATIVE_SQUARE_COUNT_OF_THE_LITERAL_GROUND_ROW
---

# Relative spectral shift: global count is free, local count is bought with definiteness we do not have

## 1. The exact ratio

On the carrier `j in {-N..N}` with Lagrange row `xi_j`, partial fractions give the
identity behind the representation:

    p(s) / prod_j (j - s)  =  sum_j xi_j/(j - s),      xi_j = p(j)/prod_{i != j}(j - i),

verified in exact rational arithmetic on both plant families of `ccbfdf4c`
(`315/512, -15/128, 1/256, ...` and `91/512, -15/128, 225/256, ...`, reproduced
fraction for fraction). So the transform's **off-lattice zero divisor** is the
numerator `p`, the **background** is the lattice `prod_j (j-s)`, and the relative
object is their ratio, which is exactly the secular function.

The scalar convention in the verdict's display, the factor `-s`, is not derivable
from the above without fixing which operator plays `D'` and on which space; I do
not reproduce it and flag it as needing a source lock before any downstream use.

## 2. Global relative count: free

`p` has degree `2N` and the background has `2N+1` poles. So over the whole real
line the zero count and the pole count differ by exactly one, for every cell and
with no hypothesis. That is the content of "the absolute mass can diverge while
the relative shift stays bounded", and it is why this representation is not
another wrapper: both counts grow like `2N`, their **difference** does not.

This closes the global question. It does not touch the local one.

## 3. Local relative count: bought only with definiteness

The plant settles the local question in the negative for the general case. Both
families have `2N = 4` roots in total. Their distribution over the four lattice
gaps is

    A:  0, 2, 2, 0        B:  2, 0, 0, 2

so the local relative shift is `+2` on some gaps and `-1` on others, in a family
where the global shift is `1`. Local boundedness by `1` is therefore **false**
without further hypotheses, even though the global bound is exact.

The hypothesis that would buy it is definiteness. If the residues `xi_j` are all
of one sign, the rank-one perturbation is definite, the secular function is
monotone across every gap, and zeros and poles **strictly interlace**: the local
count difference is at most one on every interval. That is the classical rank-one
interlacing, and it is the only route in this representation to a local bound.

But one-signed residues are precisely the configuration that makes the zero set
dense on a fixed compact, by section 2 of report `5c5a5bef` — the very thing R1
must avoid. So in this representation:

    definite  =>  local relative bound holds, but absolute zeros are dense;
    indefinite => absolute zeros may be sparse, but the local relative bound fails.

Both horns are stated as implications, not as a proof that both fail; the second
horn is "fails to follow", not "is false".

## 4. The object the horns point to

What distinguishes the two horns is not the sign pattern but the **number of sign
changes**, i.e. the number of negative squares of the indefinite inner product in
which the perturbation is self-adjoint. Writing `nu_k` for that count on cell `k`,
the classical Krein-space generalisation of interlacing bounds the local count
deviation by `nu_k` rather than by `1`.

So the exact missing object is

    KREIN_NEGATIVE_SQUARE_COUNT_OF_THE_LITERAL_GROUND_ROW:
    is the number of sign changes of the literal selected ground row, restricted
    to any central window of O(log m) modes, bounded uniformly in k?

Bounded gives a local relative bound and R1 survives; unbounded leaves the
representation without a local bound and R1 does not get past this gate. This is a
statement about one banked eigenvector and it is **not** the sign pattern itself —
correction 17 killed that — but its variation count.

## 5. Required outputs I cannot supply

Stated plainly rather than approximated.

- **Fixed-metric self-adjointness.** I did not find a source statement putting the
  free and perturbed operators in one fixed metric. With mixed-sign residues the
  natural metric is indefinite, and the relevant signature is `nu_k` of section 4.
- **Anchored log-derivative of the relative ratio.** Its representing measure is
  the signed zero-minus-pole measure, whose local mass is bounded exactly when
  section 4 is bounded. So this output is downstream of the same gate and I do not
  present it as independent progress.
- **Target crosswalk to `centeredXi`.** Removing the lattice background changes the
  function whose limit is taken. Whether the relative object still has
  `centeredXi` as its target, or a `centeredXi` divided by a background limit, is
  not established. I flag this as the `FAIL` risk the verdict names: if the
  crosswalk needs the stopped tracking rate, the representation is void.

## 6. No dead object imported

Nothing above uses the residual/graph-resolvent tracking rate, the complement
floor or the arithmetic discrepancy. Sections 1 and 2 are Lagrange partial
fractions and degree counting; section 3 is the verdict's own plant plus classical
rank-one interlacing under an explicitly stated hypothesis.

## 7. Next load-bearing gap

    KREIN_NEGATIVE_SQUARE_COUNT_OF_THE_LITERAL_GROUND_ROW

on central windows, uniformly in `k`.
