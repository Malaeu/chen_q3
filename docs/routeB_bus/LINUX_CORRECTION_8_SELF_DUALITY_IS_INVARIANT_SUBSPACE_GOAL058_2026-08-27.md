---
TASK_ID: LINUX_SELF_CORRECTION_8
MODE: PAPER_AND_SOURCE_READ_ONLY plus declared numeric check
BODY: Linux-Claude
DATE: 2026-08-27
CORRECTS: f4aea542, the queued candidate SELF_DUALITY_SUPPLIES_THE_MODE_PROFILE, item 1
STATUS: CLAIM_WEAKENED_AND_SOURCE_LOCKED
RH_CLAIM: false
---

# Correction 8 — the trial is not self-dual; its two-dimensional span is invariant

Caught before the candidate was sent to the judge, by reading the predicate that
stores the eigenrelations.

## 1. What is withdrawn

The queued candidate claimed the selected trial is an eigenfunction of the finite
Fourier action, so that its mode profile equals its spatial profile. False.

`ProlateActualModeSourceLock.lean:42`, `IsActualProlateModePair`, **requires**

    0 < P.chi2  and  P.chi2 < P.chi0.

The two production modes therefore have **different** finite-Fourier eigenvalues,
strictly ordered. A combination of eigenvectors with different eigenvalues is not
an eigenvector. So

    finiteFourierAction lambda c = chi * c

is false for the combination `c = (I4 h0 - I0 h4)/norm`, and no self-duality is
available.

I wrote the candidate from the file header of `ProlateActualModeMuntzRegularity.lean`,
which says the predicate "stores the exact nonzero finite-Fourier eigenrelations",
without opening the predicate to see that it stores **two** of them, ordered. Same
failure shape as corrections 6 and 7: a summary read instead of the definition.

## 2. What survives, and it is exact

By linearity, from the two stored eigenrelations,

    finiteFourierAction lambda c = ( I4 * chi0 * h0 - I0 * chi2 * h4 ) / norm.   (*)

So:

- the two-dimensional span `{h0, h4}` is an **invariant subspace** of the finite
  Fourier action, and the action on it is **diagonal** with entries `chi0, chi2`;
- the transform of the trial is the **same two shapes**, reweighted by two known,
  real, positive, ordered constants;
- because `chi2 < chi0`, the transform **suppresses the `h4` component relative to
  `h0`**. The Fourier side of the trial is more `h0`-dominated than the trial
  itself. That is a source-locked direction of change, not a guess.

This is weaker than self-duality and strong enough for the purpose that motivated
the candidate: the mode-side profile is explicit, not unknown. What changes is
that it carries two constants instead of one.

## 3. An internal consistency check that the design is coherent

`ProlatePair` stores `h0_fourier_center : I0 = chi0 * h0 0` and
`h4_fourier_center : I4 = chi2 * h4 0`. Substituting `h0 0 = I0/chi0` and
`h4 0 = I4/chi2` into (*) at the center gives

    ( I4 * chi0 * (I0/chi0) - I0 * chi2 * (I4/chi2) ) / norm
      = ( I4*I0 - I0*I4 ) / norm = 0,

which agrees with `finiteFourierAction_zero`, since the trial has zero integral by
construction. The two center fields are exactly what makes the transform vanish at
frequency zero as well. Nothing here is new mathematics; it confirms that my
reading of the structure is the intended one.

## 4. Numeric check, declared

`NUMERICAL_PROBE` is not authorized by any live verdict; run under the owner's
direct instruction to verify the candidate, and declared as
DIAGNOSTIC_NEVER_A_PROOF.

In the repository's own kernel convention `finiteFourierKernel x y = exp(i*2*pi*x*y)`
(`ProlateSourceRegularity.lean:19`), the *approximating* profile
`parabolicCylinderD n (projectCylinderArgument x) = exp(-pi x^2) * He_n(2 sqrt(pi) x)`
is an eigenfunction of the **full-line** transform with eigenvalue `i^n`, verified
to `8e-14` at four sample points for `n = 0..4`:

    n=0: +1        n=1: +i        n=2: -1        n=3: -i        n=4: +1

So modes `0` and `4` share the eigenvalue `+1` while mode `2` would carry `-1`.
This is why the production pair is `(0, 4)` and not `(0, 2)`: on the **shapes**,
the phase is common. The magnitudes still differ once the window is finite, which
is exactly what `chi2 < chi0` records.

## 5. Corrected candidate for the queue

Not `the mode profile is the spatial profile`, but:

    FINITE_FOURIER_INVARIANT_TWO_DIMENSIONAL_SPAN:
    the finite Fourier action maps the selected trial into the same span with
    diagonal, ordered, positive weights (chi0, chi2), so its mode-side profile is
    explicit up to those two constants; the approximating shapes are full-line
    self-dual with common phase +1.

Both caveats of the original candidate stand unchanged: the eigenrelations live in
a predicate that no file in the repository constructs, and the `O(1/lambda^2)`
approximation is a spatial sup-norm statement whose transfer to coefficients is a
separate step.

## 6. Ledger

Eleventh forbidden move: **read the predicate, not its docstring.** Three
corrections in one evening now trace to the same habit — trusting a summary line
about a definition instead of opening it. The docstring said "stores the exact
eigenrelations" and was accurate; it did not say they are equal, and I supplied
that myself.
