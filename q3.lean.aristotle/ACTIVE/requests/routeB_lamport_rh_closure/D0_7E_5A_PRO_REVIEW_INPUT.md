# D0.7e.5a — Pro review input freeze

Status: `EXTERNAL_REVIEW_TRANSCRIPT / NOT_PROOF_AUTHORITY / NOT_RH`

Captured: 2026-07-12 10:16 CEST.

This file freezes the operational content of the latest Proshka reply that the
owner explicitly asked Codex to read in the in-app browser. It is a Codex
transcription of that browser reply, not an author-signed mathematical source.
The physical file `D0_7E_5_PRO_REVIEW_DECISION.md` remains a separate owner
input and is not edited here. Any conflict between the two inputs must be
audited rather than silently resolved.

## Target

```text
D0.7e.5a WPrimeConsumerAndCalibrationOrientationLock
```

## Mandatory review ruling

1. Treat `D0_7E_CENTRAL_CALIBRATION_LOCKED` only as the finite central
   calibration ratio.
2. Locate independent authoritative definitions of the normalized ZEO
   approximant `FZeo_(m,N)` and of `WPrime_(m,N)` before accepting any
   consumer identity.
3. Determine whether the normalization is written as a multiplier or a
   divisor. With

   ```text
   bCal_(m,N)=Fhat_(m,N)(0)/Xi(0),
   ```

   the central-value normalized approximant is

   ```text
   Fhat_(m,N)/bCal_(m,N)
   = bCal_(m,N)^(-1) Fhat_(m,N).
   ```

   Therefore a multiplier coefficient for the normalized approximant is the
   inverse of `bCal`, not `bCal` itself.
4. Do not infer central nonvanishing from `TrialNonzero`.
5. Do not define `WPrime` by the desired right-hand side merely to make the
   crosswalk true. The consumer must exist independently first.
6. Retain both indices `(m,N)`; do not invent `N(lambda)`.
7. Do not import H3c, H4, asymptotics, or a new physical Bus 010.

## Success and stop vocabulary

Success, only if an independent consumer and its orientation are pinned:

```text
D0_7E_B_ORIENTATION_LOCKED
```

Fail-closed codes include:

```text
D0_7E_WPRIME_CONSUMER_MISSING
D0_7E_ZEO_NORMALIZATION_ORIENTATION_MISSING
D0_7E_TRIALNONZERO_NOT_CENTRALNONZERO
D0_7E_BCAL_ZERO_OR_UNPROVED
D0_7E_BCAL_BZEO_ALIAS_CONFLICT
D0_7E_SOURCE_NORMALIZATION_CONFLICT
D0_7E_D0_DEPENDENCY_CYCLE
D0_7E_SELECTOR_INVENTED
```

The review does not authorize a `PROVED` label. It defines the audit required
to decide whether `D0.7e.5a` can be closed.
