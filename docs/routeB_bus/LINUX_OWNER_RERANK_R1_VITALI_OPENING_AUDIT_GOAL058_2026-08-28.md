---
TASK_ID: LINUX_OWNER_RERANK_R1_OPENING_AUDIT
MODE: PAPER_AND_SOURCE_READ_ONLY
BODY: Linux-Claude
DATE: 2026-08-28
AUTHORITY: owner decision this session — "go R1"
RESPONDS_TO: 9759aa5c (OWNER_RERANK required, R1 reentry condition OWNER_AUTHORIZED_ACQUISITION)
DISCRIMINATOR: not a transaction — an opening audit and a request
EXECUTION_AUTHORIZED: false, pending judge
LEAN_EDIT: false
NUMERICS: none
RH_CLAIM: false
---

# Owner rerank: R1 selected. What the shelf already holds, and the two inputs that remain

## 0. The decision

The owner selects **R1**, the Vitali/Montel qualitative route: keep the same
normalized finite ground transforms, and replace the consumer-strength tracking
rate by **local boundedness plus a nonzero anchor**, letting Montel and the
identity theorem supply locally uniform convergence. This satisfies R1's reentry
condition `OWNER_AUTHORIZED_ACQUISITION` in verdict `9759aa5c`.

Recorded here before any work, per the precommit rule. No transaction is opened
by this document; the judge's directive is requested at the end.

## 1. The machinery is already banked, and kernel-green

Asked the shelf before proposing anything. `D0PostAnchorMontel.lean` and
`MontelCenteredCriticalStrip.lean` already contain the whole apparatus:

- `isPreconnected_centeredCriticalStrip` (line 17) — the domain is preconnected,
  which is what the identity theorem needs;
- `montel_centeredCriticalStrip_exists_subseq_tendstoLocallyUniformlyOn`
  (line 175) — Montel compactness for holomorphic functions locally bounded on
  the centered critical strip, with `#print axioms` at line 273;
- `montel_centeredCriticalStrip_anchor_nonzero_limit` (line 238) — a fixed
  nonzero anchor forces every Montel limit to be locally nonzero, `#print axioms`
  at line 274;
- `selectedFamily_locallyBounded_of_raw_bound_and_central_floor`
  (`D0PostAnchorMontel.lean:73`, `#print axioms` at line 168) — the assembly;
- `montelRefinement` — absorbs Montel's strict subsequence into the existing
  extraction **without** changing the coefficient family, the parent path or its
  cofinality. That is the guard against a subsequence quietly replacing the
  selected family.

So R1 does not require building an apparatus. It requires discharging two
hypotheses.

## 2. The two hypotheses, verbatim

    SelectedRawLocallyBounded D :=
      forall K compact, exists M >= 0, forall k, forall z in K,
        || rawFplus D.kTrial (D.parent (D.extract k)).1 z || <= M

    SelectedCentralFloor D :=
      exists delta > 0, forall k,
        delta <= || rawFplus D.kTrial (D.parent (D.extract k)).1 0 ||

Both are statements about the **raw transforms of the selected family**. Neither
is a rate, neither mentions the graph resolvent `C^{-1}`, neither mentions the
complement floor, and neither mentions the arithmetic. That is the structural
reason R1 is not the line that just died: the objects that defeated us —
`C^{-1}`, the Stieltjes discrepancy, the observability envelope — do not appear.

## 3. The central floor is close to supplied

`D0AnchorFloor.lean:86`, `D0AnchorFloorFromUnprojectedCentralMass`, concludes
per index `i`, among other things,

    a/C <= || rawFplus D i 0 ||,

which is exactly the body of `SelectedCentralFloor`. Its hypotheses are

    a <= sqrt(L_m i) * || <V_0, g> ||        (central Fourier mass of the
                                              unprojected trial),
    || g || <= C                              (unprojected trial norm),

with `g = gTrial_m i hTrial_m hE_star`. The companion
`D0AnchorFloorFromUnprojectedMassNormRatio` (line 167) gives the same conclusion
from a **ratio** hypothesis, which is the more usable form because it is
scale-free.

So `SelectedCentralFloor` reduces to making `a` and `C`, or the ratio `delta`,
**uniform along the selected schedule**. That is a statement about the prolate
construction alone. I do not claim it is easy; I claim it is the right size and
lives entirely in objects we build.

## 4. What is genuinely open

    R1_A: SelectedRawLocallyBounded — a uniform compact sup bound for the raw
          transforms along the selected sequence.
    R1_B: uniformity of the anchor-floor constants along the selected schedule,
          which then discharges SelectedCentralFloor through D0AnchorFloor.

And, separately, the identification of the Montel limit. Montel supplies a
convergent subsequence with a nonzero limit; identifying that limit with the
target requires convergence on a uniqueness set, or all jets at one anchor, on
the preconnected strip. `D0CriticalMomentCanonicalCluster` and
`D0CriticalMomentMontelGate` exist and were not audited in this pass; that is the
first thing the opened transaction should read.

## 5. The mandatory guard, restated so it is not violated later

Verdict `9759aa5c` requires: local boundedness must come from real-zero, Cauchy
or de Branges structure, and **may not assume the missing tracking rate under
another name**. Concretely, `R1_A` must not be derived from any bound of the form
"the residual is small", because that is the dead object. It must come from the
transform's own structure — the `2 sin(zL/2)` numerator, the pole-kernel
representation, the entire extension — or from a real-zero interlacing argument.

I flag in advance that this is where an error would be easiest to make, and it is
the same failure mode as forbidden move 12: carrying a quantity the route already
lost, under a new name.

## 6. Request to the judge

Open a transaction for R1 with, at minimum:

1. audit of `D0CriticalMomentCanonicalCluster`, `D0CriticalMomentMontelGate` and
   the uniqueness-set machinery;
2. the exact reduction of `SelectedCentralFloor` to uniform anchor-floor
   constants, via `D0AnchorFloorFromUnprojectedMassNormRatio`;
3. a precommitted statement of where `SelectedRawLocallyBounded` is to come from,
   with the guard of section 5 stated as a discriminator rather than a hope.

Nothing above is executed. No Lean, no numerics, no new object.
