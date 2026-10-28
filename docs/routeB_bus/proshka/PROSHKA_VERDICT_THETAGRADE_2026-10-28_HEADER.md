# THETAGRADE verdict — header only (2026-10-28)

The owner pasted the result header into the Linux chat. The full attachment
PROSHKA_VERDICT_THETAGRADE_2026-10-28.md is NOT yet on disk; the content below is the header verbatim.

```
OPERATIVE_CLASS: RUN_THETAGRADE_DISCRIMINATOR
REQUEST_ID: REQ-2026-10-28-THETAGRADE
BOUNDARY_ID: GOAL058_ROPES_THETA_GRADING
SOURCE_BASE_COMMIT: 4a847548e3ee45b2f8a548349110ceb437abe3a4
Q1a: WITNESS_CONFIRMED_CONDITIONAL
Q1b: WITNESS_CONFIRMED_CONDITIONAL
Q1c: WITNESS_GAP_ARBITRARY_THETA_UPPER_AND_ENDPOINT
Q1iii: WITNESS_CONFIRMED_CONDITIONAL
Q2: G1_UNDECIDED_FIRST_FACT
Q3: SOURCE_VERIFICATION_INCOMPLETE
PROGRESS_CLASS: REPRESENTATION_PROGRESS
ROUTE_SCORE: 3
PX_RH_CLAIM: NOT_MADE
REPO_WRITTEN: false
LEAN_EXECUTED: false
```

## Pre-registered predictions vs header (observer, provisional until the attachment is read)

| Prediction | Probability | Header | Score |
|---|---|---|---|
| P1 Q1a, Q1b confirmed with hypotheses {G1, G2, G4, G3c, hmode/hchi, T5} | 0.80 | CONFIRMED_CONDITIONAL | hit on the code; hypothesis list not yet checked |
| P1c Q1c for arbitrary Theta | 0.75 | GAP (upper side and endpoint) | miss |
| P1t Q1(iii) any route | 0.85 | CONFIRMED_CONDITIONAL | hit |
| P2 NOT_GRADED 0.50 / THETA_WITNESS 0.35 / UNDECIDED 0.15 | | UNDECIDED_FIRST_FACT | miss: the lowest-probability branch |
| P3 DEGREE_FROM_OBJECT 0.70 / FORCED 0.20 / DISAGREES 0.10 | | SOURCE_VERIFICATION_INCOMPLETE | no score: code outside the registered set |

Open until the attachment: the exact first fact for Q2, the exact gap in Q1c, and what part of qrh78 was not read.
