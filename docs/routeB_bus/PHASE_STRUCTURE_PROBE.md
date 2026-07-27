# SOFT_2 PhaseStructureProbe

Status: `FLOAT64_DIAGNOSTIC / NOT_THEOREM / NOT_RH`

The object is `H=Xi(0)B/B(0)` with the completion gauge removed.
The axial phase statistic is branch-safe modulo pi.  Sampled zero-floor
points and one neighboring grid point on each side are excluded.
The registered `PHASE_SLOPE_EQUALS_LOG_LAMBDA_DIAGNOSTIC` compares the
fitted slope with `L/2=log(lambda)`.  Agreement is a half-shift signature
and a completion-gauge consistency check only.  It is diagnostic input
for the V1 parity-closure question, not a parity theorem and not RH.

| (m,N) | sd(theta mod pi) | mean mod pi | axial R | drift slope | slope-log(lambda) | excursion | R2 | excluded | code |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---|
| (13,120) | 0.899909670459 | 0.618364268257 | 0.00959468772416 | 1.28238627476 | -8.84039670033e-05 | 49.8022357135 | 0.999996778982 | 0 | `C2_PHASE_FREE` |
| (14,120) | 0.899158678813 | 0.288440237446 | 0.0159521174639 | 1.31956193967 | 3.32748630951e-05 | 51.2459748294 | 0.999999356703 | 0 | `C2_PHASE_FREE` |
| (53,120) | 0.894244789176 | 0.037896736956 | 0.0217784038076 | 2.00748760794 | 0.022341651167 | 77.9619783916 | 0.999312874452 | 0 | `C2_PHASE_FREE` |
| (101,120) | 0.898724012766 | -0.992651719717 | 0.0140260356478 | 2.29068001482 | -0.016880243603 | 88.9599243904 | 0.999486301507 | 0 | `C2_PHASE_FREE` |

Verdict: `C2_PHASE_FREE`.
Diagnostic: `PHASE_SLOPE_EQUALS_LOG_LAMBDA_DIAGNOSTIC`.
The diagnostic preserves `C2_PHASE_FREE`.

This probes C2 as stated. It is not proof of a packet symmetry, S2, or RH.
