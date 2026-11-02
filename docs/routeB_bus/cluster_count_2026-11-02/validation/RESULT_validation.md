# Independent cluster-count validation

Fresh literal even-carrier matrices at 140 dps and eight-panel GL160; m=N=8,24,40. The shared analytic matrix formula is unchanged, while precision and quadrature order are increased relative to the main 100 dps/GL128 scan. This checks numerical stability, not an independent analytic derivation or interval enclosure.

|m|B=2 count|B=4 count|B=8 count|N(2πm/log m)|N(2πm)|
|---:|---:|---:|---:|---:|---:|
|8|5|4|3|2|10|
|24|14|13|10|8|53|
|40|22|20|18|16|109|

Counts use abs(lambda)<m^(-B). Stored positive zeta ordinates are counted strictly below each cutoff; the preceding and following ordinate and both margins are retained. The smallest relative eigenvalue-to-threshold margin over these nine checks is 0.10657145907275087.

comparison.json records main-versus-validation count equality and the maximum absolute spectral difference divided by each threshold margin. Tiny bottom eigenvalue relative accuracy is not used to justify these classifications.

Replay: `uv run --with mpmath validate.py`, then `uv run --with mpmath compare.py` after the main spectra exist.

All nine main-versus-validation counts agree. Maximum absolute spectral discrepancy: 1.2398119907804018e-99. Maximum spectral discrepancy divided by the relevant threshold margin: 1.0375151883353207e-86.
