# Cluster-count test, literal even CCM

**DIAGNOSTIC_NEVER_A_PROOF.**

Every integer m=8,…,40 uses N=m, L=log m and dimension d=m+1. The scan uses 100 decimal digits and eight-panel GL128 quadrature; m=8,24,40 are recomputed at 140 digits/GL160. This is numerical validation, not interval certification.

Write C_B=#{i: |lambda_i|<m^(-B)}, P=d−N_zeta(2πm/log m), Q=d−N_zeta(2πm). All tuples below are ordered B=(2,4,8). Zero counts use strict positive ordinates below the cutoff. The existing 180-digit zero table through height 300 covers every cutoff in this scan. Since N=m, the requested 2πN/L comparison is exactly the P comparison.

|m|C₂, C₄, C₈|P|C−P (B=2,4,8)|Q|C−Q (B=2,4,8)|
|---:|:---|---:|:---|---:|:---|
|8|5, 4, 3|7|-2, -3, -4|-1|6, 5, 4|
|9|6, 5, 4|7|-1, -2, -3|-2|8, 7, 6|
|10|6, 5, 4|8|-2, -3, -4|-3|9, 8, 7|
|11|7, 6, 4|9|-2, -3, -5|-4|11, 10, 8|
|12|8, 7, 5|10|-2, -3, -5|-5|13, 12, 10|
|13|8, 7, 5|10|-2, -3, -5|-7|15, 14, 12|
|14|8, 8, 6|10|-2, -2, -4|-9|17, 17, 15|
|15|9, 8, 6|11|-2, -3, -5|-10|19, 18, 16|
|16|10, 9, 7|12|-2, -3, -5|-12|22, 21, 19|
|17|10, 9, 7|12|-2, -3, -5|-14|24, 23, 21|
|18|11, 10, 8|13|-2, -3, -5|-16|27, 26, 24|
|19|11, 10, 8|14|-3, -4, -6|-18|29, 28, 26|
|20|12, 11, 9|14|-2, -3, -5|-20|32, 31, 29|
|21|12, 11, 9|14|-2, -3, -5|-22|34, 33, 31|
|22|13, 12, 10|15|-2, -3, -5|-24|37, 36, 34|
|23|14, 12, 10|16|-2, -4, -6|-26|40, 38, 36|
|24|14, 13, 10|17|-3, -4, -7|-28|42, 41, 38|
|25|15, 13, 11|17|-2, -4, -6|-30|45, 43, 41|
|26|15, 14, 11|17|-2, -3, -6|-33|48, 47, 44|
|27|15, 14, 12|18|-3, -4, -6|-35|50, 49, 47|
|28|16, 15, 12|19|-3, -4, -7|-37|53, 52, 49|
|29|16, 15, 13|19|-3, -4, -6|-40|56, 55, 53|
|30|17, 16, 13|20|-3, -4, -7|-42|59, 58, 55|
|31|18, 16, 14|20|-2, -4, -6|-44|62, 60, 58|
|32|18, 17, 14|21|-3, -4, -7|-46|64, 63, 60|
|33|19, 17, 15|22|-3, -5, -7|-49|68, 66, 64|
|34|19, 18, 15|22|-3, -4, -7|-52|71, 70, 67|
|35|20, 18, 16|22|-2, -4, -6|-54|74, 72, 70|
|36|20, 19, 16|23|-3, -4, -7|-57|77, 76, 73|
|37|21, 19, 16|24|-3, -5, -8|-60|81, 79, 76|
|38|21, 20, 17|24|-3, -4, -7|-62|83, 82, 79|
|39|22, 20, 18|25|-3, -5, -7|-65|87, 85, 83|
|40|22, 20, 18|25|-3, -5, -7|-68|90, 88, 86|

## What the scan supports

- B=2: modal-count offset ranges from -3 to -1; at m=8 it is -2, and at m=40 it is -3.
- B=4: modal-count offset ranges from -5 to -2; at m=8 it is -3, and at m=40 it is -5.
- B=8: modal-count offset ranges from -8 to -3; at m=8 it is -4, and at m=40 it is -7.

No single constant offset holds on this finite range, even with B fixed. These cells do not decide whether a bounded, threshold-dependent edge correction holds asymptotically. The 2πm substitution gives negative Q throughout the range, so it cannot itself be a dimension/count formula here. The Connes–Consani height scale should not be substituted for a finite Fourier-carrier cutoff without another argument.

The smallest relative distance to an absolute threshold is 0.01609698216. Negative levels outside the tested absolute bands: 0. Thus signed and absolute counts agree in these cells. Raw tiny eigenvalue signs remain numerical quantities; this does not establish a cofinal floor.

## The NOESCAPE consumer

L12 requires the signed count #{lambda<mu}≤r and a genuine r-dimensional subspace J satisfying ||A restricted to J||≤delta<mu. Its proof and the growing-rank floor route L13 remain valid. An absolute count alone misses every lambda≤−mu. Finite zero interpolation does not by itself establish the conditioned operator residual or full radicality.

Equation (5.9) is a fixed-rank package. A growing dimension-minus-zero-count proposal instead needs the growing-rank residual package (5.4); fixed-order theta-jet decay does not automatically provide it. See THEOREM_CHECK.md for exact source lines and the negative control.

## Reproduction and files

Run `uv run --with mpmath python3 scan.py 8 9 ... 40`, then `scan.py summarize`, then `validation/validate.py`, `validation/compare.py`, and `report.py`. The ellipsis means all intervening integers; scan.py accepts an explicit integer list. The shared matrix implementation is ../phase_space_V/v_forms.py; its SHA256 is recorded in each spectrum. The zero-table SHA256 is in metadata.json.

counts.csv contains all 99 threshold comparisons, signed counts, both zero counts, and margins. spectra.csv and per-cell JSON preserve every eigenvalue. validation/ contains the higher-precision replay and comparison. No source matrix or route status is changed.
