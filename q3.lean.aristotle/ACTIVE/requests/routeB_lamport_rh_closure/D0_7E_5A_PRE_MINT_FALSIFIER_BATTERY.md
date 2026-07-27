# D0.7e.5a pre-mint falsifier battery

Status: `INVALID_EXECUTABLE_SPEC_AS_WRITTEN / MINT_MENU_REVISION_REQUIRED / NOT_RH`.

| probe | literal score | decisive finding |
|---|---|---|
| P1 | FAIL | R2 uses kTrial, but full persisted Mfin/xi data are incomplete |
| P2 | FAIL | R2 formula is repaired; factor test is nondiscriminating and Rayleigh-alpha 5c fails |
| P3 | PASS | planted `SLOT_VACUITY` fires |
| P4 | FAIL | no registered tolerance; raw slope depends on carrier |

R2's repaired `kTrial` line makes the reduced S0 P1
residuals `5.68e-16`, `1.83e-16`, `3.80e-16`, all below `1e-12`,
but S0 is a diagnostic Schur object, not canonical Mfin.

P2 R2's orientation ratios equal `|bCal|^4` (about 0.123) exactly as
registered, but this is algebraic for both the wrong and repaired
alpha formula and cannot choose orientation. Every bCal is within a
factor ten of one, so the declared outcome is ZERO_CONSISTENT_UNDECIDABLE.
For the registered two-level Rayleigh-excess candidate, the direct
5c closure ratios are about `6.94e-102`, `4.91e-102`, `2.51e-112`,
not one.

P4 at N=120 gives beta_W=-321.891809286 on the reduced two-level
carrier and beta_W=4.71336008648 on the full float64 residual proxy;
both satisfy beta_W-beta_r=0.5 by definition, so that increment is
not an independent falsifier.

D0.7e.5a remains BLOCKED/ACTIVE. Mint inactive. No Bus 010.
