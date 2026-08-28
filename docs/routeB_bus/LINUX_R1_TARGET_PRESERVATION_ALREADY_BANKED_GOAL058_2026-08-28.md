---
TASK_ID: GOAL058_R1_TARGET_PRESERVATION_CATALOGUE_ANSWER
MODE: DERIVATION_PLUS_EXACT_RATIONAL_CHECK_PLUS_CATALOGUE_READ
BODY: Linux-Claude
DATE: 2026-08-28
RESPONDS_TO: owner selection of option 1 after 8aff714d
DISCRIMINATOR: ANSWERED_FROM_OUR_OWN_SHELF
RESULT_CODE: TARGET_PRESERVATION_IS_KERNEL_GREEN_SINCE_2026_08_12_BUT_BUYS_ONLY_THE_PER_CELL_TRANSFER
LEAN_EDIT: false
NUMERICS: exact rational only; no floating-point probe
RH_CLAIM: false
CLOSES:
  - R1_TARGET_CROSSWALK_TO_CENTEREDXI (in the zero-set direction)
  - P59_MINUS_S_SCALAR_CONVENTION_FLAG
OPENS: []
---

# The theorem option 1 was going to buy is already ours, and it does less than hoped

## 1. What the owner selected

Option 1 of the rerank: acquire the target-preservation theorem for the relative
spectral shift. The judge's framing: "the relative object is a candidate that costs
a target-preservation theorem, not a free adapter." My own preflight `91e40850`
listed the crosswalk as a required output I could not supply, and named it the
`FAIL` risk: if the crosswalk needs the stopped tracking rate, the representation
is void.

## 2. The derivation, before the catalogue

The relative object is the secular sum after removing the lattice background. In
the mode variable the background is `prod_{j=-N}^{N} (j - s)`. Exact factorization,
verified coefficient by coefficient in rational arithmetic for `N = 1..12`:

    prod_{j=-N}^{N} (j - s) = (-1)^N (N!)^2 * (-s) * prod_{n=1}^{N} (1 - s^2/n^2).

The `j = 0` term is the factor `(-s)`. **This closes my own flag** from `91e40850`
section 1, where I wrote that the verdict's scalar convention "the factor `-s`" was
not derivable and needed a source lock. It is the `j = 0` term of the background,
nothing else.

The normalized background therefore tends to `-sin(pi s)/pi` by Euler's product.
Mathlib has that limit as `Complex.tendsto_euler_sin_prod`
(`Mathlib/Analysis/SpecialFunctions/Trigonometric/EulerSineProd.lean:285`),
**pointwise**, not locally uniformly.

In the transform variable the correspondence is `s = z L / (2 pi)`, because
`proposition59Pole L k = 2 k pi / L` (`Proposition59EntireTransform.lean:13`). So
the background is `sin(z L / 2)`, that is the Proposition-5.9 sine numerator.

## 3. Then I asked the shelf, and it was already there

**`proposition59RawTransform_eq_paper_formula`**
(`q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59EntireTransform.lean:119`),
kernel-green, off the finite lattice with `L != 0`:

    proposition59RawTransform L S xi z
      = (sqrt L)⁻¹ * proposition59Numerator L z * sum_k xi k / (z - proposition59Pole L k).

That is the factorization above, already proved. My derivation reproduced an
existing theorem.

**`proposition59Numerator_zero_im`**
(`Proposition59GroundLagrangeZeroSetBridge.lean:214`): a zero of the sine numerator
has `im = 0` when `L != 0`. The background contributes **only real zeros**.

**`proposition59CCMTransform_zerosRealOn_of_lagrange`**
(same file, line 231): if the Lagrange polynomial — the relative object's numerator
— has only real zeros, then the exact P59 transform has only real zeros. The proof
carries the three required branches: an included removable pole, an exterior zero
of the sine numerator, and an off-lattice Lagrange zero.

**`Proposition59GroundLagrangeZeroSetBridge`** (line 341) is the public wrapper.

All of it dated 2026-08-12, with a knowledge preflight receipt in its own header.

## 4. The honest verdict on option 1

**The target-preservation theorem does not need buying.** In the direction that
matters for real-zeroness it is our own, kernel-checked, and six weeks old. The
judge's cost estimate was wrong in our favour, and my preflight listed as
unsupplied something the catalogue already supplies.

**But it buys less than the rerank hoped.** What is preserved is the *zero set*,
per cell, at fixed `k`: removing the background deletes only real points, so a
non-real zero of the transform is a non-real zero of the relative object and back.
What is **not** preserved is the *limit*.

The background factor is `2 sin(z L_k / 2) / sqrt(L_k)` with `L_k = log m_k`
growing. On any fixed compact off the real axis `|sin(z L / 2)|` grows like
`exp(|Im z| L / 2)`, so — given the local boundedness of the transforms, which is
`R1_B` and is banked only conditionally — the relative family tends to zero off the
real axis. It degenerates exactly as the mandatory plant of the object lock
`9ff604bd` section 5 degenerates.

So the relative representation is a legitimate **zero-counting device on each fixed
cell**, which is where the Krein negative-square question lives, and it is **not** a
carrier for the Hurwitz limit. The limit must still be taken on the transform.

## 5. What this does and does not change

Changed: `R1_TARGET_CROSSWALK_TO_CENTEREDXI` is closed in the zero-set direction and
is no longer a `FAIL` risk; the `-s` scalar flag is closed; option 1 costs nothing
to acquire.

Not changed: `KREIN_NEGATIVE_SQUARE_COUNT_OF_THE_LITERAL_GROUND_ROW` stays the load
-bearing gap, exactly as `91e40850` left it. Nothing here supplies a rate, and
nothing here revives the tracking corridor.

## 6. Process note

I derived section 2 before querying the catalogue, and the catalogue then returned
the finished theorem. The rule held: the derivation was not reported as a finding
until the shelf had answered. Recording it because this is the fourth instance of
the same pattern in the project record — the thing existed, and the query was the
cheap step.
