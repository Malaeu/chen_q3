---
TASK_ID: LINUX_OWNER_ORDERED_VERIFICATION_OF_ONE_MEASURE_CLAIM
MODE: LEAN_KERNEL_PLUS_NUMERIC_DIAGNOSTIC
BODY: Linux-Claude
DATE: 2026-08-27
VERIFIES: 5a02a6fd section 3 (completed beta is a single spectral measure)
AUTHORITY: owner instruction, this session, "проверь это ещё раз ... особенно про то, что все три вещи в формуле это одно и то же"
LEAN_EDIT: true
LEAN_COMMIT: 2aaff3e7
NUMERICS: DIAGNOSTIC_NEVER_A_PROOF, declared, not authorized by verdict 3f4c23eb
RH_CLAIM: false
CLOSES:
  - ONE_MEASURE_CLAIM_UNVERIFIED
OPENS:
  - SOURCE_BETA_POSITIVE_AT_A_POSITIVE_MODE_ANALYTIC_PROOF
---

# Verification of the one-measure claim

The owner ordered a re-check of the claim in `5a02a6fd` that the three ledgers
of the finite explicit formula collapse to one spectral object. Two independent
checks were run. Both confirm the claim. One of them also produced a finding
about the Ricci sign gate that is recorded below and is *not* a proof.

## 1. Kernel check

New file, commit `2aaff3e7`:

    q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCenterSpectralNormalForm.lean

Seven public declarations, all with axiom triple
`[propext, Classical.choice, Quot.sound]`, hole scan clean, module built with
`lake build` exit 0:

- `ccmQKernel_center` — at the center the CCM kernel takes its off-diagonal
  branch and equals `-sin(2 pi n x / L)/(pi n)`;
- `ccmQKernel_center_zero` — it vanishes at `x = 0`;
- `ccmW02Entry_center` — `ccmW02Entry L n 0 = 32 L sinh(L/4)^2 / (L^2 + 16 pi^2 n^2)`;
- `ccmWRIntegrand_center` — with the explicit factor `n` cancelled;
- `ccmWREntry_center` — the Euler-Mascheroni head is *gone* and the ledger is a
  sine transform against `exp(x/2)/(2 sinh x)` on `(0, L]`;
- `ccmPrimeEntryN1_center` — the factor `n` cancels and the ledger is a sine
  transform against the von-Mangoldt atoms at `log k`;
- `ccmBetaScalar_center_spectral_normal_form` — the assembled statement.

The assembled theorem, verbatim from the file, for `n != 0` and `ccmL m != 0`:

    ccmBetaScalar m n
      = 32 * L * sinh(L/4)^2 * n / (L^2 + 16 pi^2 n^2)
      + (1/(2 pi)) * integral_{Ioc 0 L} exp(x/2) * sin(2 pi n x / L) / sinh x
      + (1/pi)     * sum_{k in Icc 2 m} Lambda(k) * (sqrt k)^{-1} * sin(2 pi n (log k) / L)

The three summands share the argument `2 pi n * (length) / L`. The archimedean
ledger and the prime ledger differ only in the measure against which that sine
is integrated: an absolutely continuous density in one case, von-Mangoldt atoms
in the other, on the same interval `(0, L]`. This is the claim, now kernel-green.

Two structural facts came out of the proofs rather than being assumed:

- the whole Euler-Mascheroni head of `ccmWREntry` is deleted at the center,
  because `ccmQKernel L n 0 0 = 0`; nothing was dropped by hand;
- the explicit factor `n` of `ccmBetaScalar` cancels against the `1/(pi n)` of
  the off-diagonal kernel branch in *both* the archimedean and the prime ledger,
  which is why they land on the same axis at all.

## 2. Numeric check, declared

Independent transcription of the literal Lean definitions into a separate
evaluator, compared against the normal form above at `m = 12, 50, 200` and
`n = 1, 2, 3, 5, -1, -4`. Agreement to `<= 3.6e-16` absolute in every cell,
i.e. machine precision. Oddness `beta_{-n} = -beta_n` reproduced to `1e-12`.

The pole ledger was additionally checked in three forms — closed rational,
half-line integral `integral_0^infty exp(-Lt/(4 pi)) sin(n t) dt` with the
prefactor `2 L sinh(L/4)^2 / pi^2`, and the same folded onto `(0, 2 pi]` with
density divided by `1 - exp(-L/2)`. All three agree to `7e-10` or better. The
folding matters: it places the pole ledger on `(0, 2 pi]` as well, so the whole
completed field lives on one bounded angle interval.

Magnitudes at `m = 200, n = 1`: pole `+2.783`, archimedean `+0.312`,
prime `-3.080`, total `+0.0149`. The cancellation between the pole and prime
ledgers is about two orders of magnitude at this size and grows with `m`.

## 3. Unplanned finding: the Ricci sign gate

The evaluator also returns, at every `m` tested (12, 50, 200, 1000, 5000,
20000), a *positive* value `beta_1 > 0`. Since `beta_0 = 0` by the explicit
factor `n`, this means `Delta beta_0 = beta_1 - beta_0 > 0`.

By the judge's own sharpened criterion in verdict `3f4c23eb` — one positive
first difference on the nonnegative half kills the strict Doob sign gauge — the
gate would then fail. In other words the conclusion of the withdrawn report
`c1e5f00f` looks correct even though its proof was not.

**This is a diagnostic and nothing more.** It does not reinstate the FATAL. The
missing supplier is still

    SOURCE_BETA_POSITIVE_AT_A_POSITIVE_MODE

and it is still unproved. Proving `beta_1 > 0` is not cheap: `beta_1` is a
difference of two quantities of size `~ sqrt m` leaving a remainder of size
`~ 1/log m`, so the positivity of the remainder is a cancellation statement, not
an inequality between visible terms. Correction 5 stands unchanged.

Recorded per the standing rule that anything odd is written down when noticed,
together with both readings: either `beta_1 > 0` holds for a structural reason
still to be found, or the sampled sizes are unrepresentative. The outcome that
separates them is an analytic lower bound on `beta_1`, not more sampling.

## 4. Declaration

Verdict `3f4c23eb` set `LEAN_EDIT_AUTHORIZED: false` and
`NUMERICAL_PROBE_AUTHORIZED: false` for the completed-spectrum transaction. Both
were performed here on the owner's direct instruction to verify the one-measure
claim, which outranks the transaction scope. The Lean file adds no axiom, no
`sorry`, and no new definition — only rewrites of existing source definitions.
Nothing in `5a02a6fd` was edited; this file is additive.
