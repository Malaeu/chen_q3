# LadderLaw_v1_Addendum

ZERO compute addendum. Extraction from saved JSONs only:
`out/ladder_law_v1.json`, `out/parity_block_lambda_sq_{12,13,14}_N_120.json`.
No Phase 2. No new matrices. No new inverse iteration. Not RH.

## A1 Rung Residuals And PSD Judge

| rung | mu | eigen-residual | residual <= 1e-60 | PSD clean line | PSD clean silent |
|---:|---:|---:|---|---|---|
| 4 | `4.24957812883217e-48` | `1.06559475406380e-76` | `True` | `E_tail=4.24957796506379e-48 <= threshold=4.43660430196748e-48` | `True` |
| 5 | `1.09069940322272e-44` | `1.52743360218546e-68` | `True` | `E_tail=1.09069931983028e-44 <= threshold=1.09163690892037e-44` | `True` |
| 6 | `2.01792832867329e-41` | `1.48383114434507e-60` | `False` | `E_tail=2.01792832867329e-41 <= threshold=2.01796864520108e-41` | `True` |

PSD judge was silent on the clean vectors for all three rungs. Registered residual threshold has one small numeric miss at rung 6: `1.48e-60` vs `1e-60`.

## A2 Gap Slope And W-prime Decomposition

Fit from saved N=120 parity-block values:

| lambda_sq | mu3-mu1 | `(mu3-mu1)/E` |
|---:|---:|---:|
| 12 | `1.69321145766379e-46` | `5.23330664613522e+19` |
| 13 | `1.31185429988032e-51` | `1.16266875847804e+20` |
| 14 | `9.38433376247524e-57` | `2.38494990133893e+20` |

- gap slope: `19.6819692055`; registered `19.4 +- 1.5`: `PASS`.
- raw alpha/E slope: `8.67649202592`.
- raw W-prime slope: `-5.00273858981`.
- decomposition:

```text
measured W' slope -5.00273858981
= 0.5 + (8.67649202592 - 19.6819692055)/2
```

The registered W-prime slope window `-3.5 +- 0.7` is missed in the favorable direction: measured decay is faster (`-5.0`).

## A3 State Score

- `W_prime` slope registered miss: target `-3.5 +- 0.7`, measured raw `-5.00273858981`, favorable direction, `FIT_NOT_LAW`.
- `gap/E` slope registered pass: target `19.4 +- 1.5`, measured `19.6819692055`.
- rung residual registered note: rung 6 is `1.48x` above the `1e-60` residual floor; PSD clean judge remains silent for all rungs.
- `G4'` marking:
  - `CONDITIONAL(RH-regime)` as theorem candidate;
  - `UNCONDITIONAL` as detector component only.

## Handoff

Stop after this addendum and handoff. Next accepted step: pen, only after reviewer accepts the `RH-EQUIVALENT GATE` marking and finite-N caveat.
