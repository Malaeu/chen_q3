"""Render the finite count comparison; DIAGNOSTIC_NEVER_A_PROOF."""
import csv,json
from pathlib import Path
P=Path(__file__).resolve().parent
rows=list(csv.DictReader((P/'counts.csv').open()))
lines=['# Cluster-count test, literal even CCM', '', '**DIAGNOSTIC_NEVER_A_PROOF.**', '',
'Every integer m=8,…,40 uses N=m, L=log m and dimension d=m+1. The scan uses 100 decimal digits and eight-panel GL128 quadrature; m=8,24,40 are recomputed at 140 digits/GL160. This is numerical validation, not interval certification.', '',
'Write C_B=#{i: |lambda_i|<m^(-B)}, P=d−N_zeta(2πm/log m), Q=d−N_zeta(2πm). All tuples below are ordered B=(2,4,8). Zero counts use strict positive ordinates below the cutoff. The existing 180-digit zero table through height 300 covers every cutoff in this scan. Since N=m, the requested 2πN/L comparison is exactly the P comparison.', '',
'|m|C₂, C₄, C₈|P|C−P (B=2,4,8)|Q|C−Q (B=2,4,8)|',
'|---:|:---|---:|:---|---:|:---|']
for m in range(8,41):
 r=[x for x in rows if int(x['m'])==m]
 triple=lambda key:', '.join(x[key] for x in r)
 lines.append(f"|{m}|{triple('count_abs_lambda_lt_mu')}|{r[0]['prediction_dimension_minus_Nzeros_Tlog']}|{triple('abs_count_minus_log_prediction')}|{r[0]['prediction_dimension_minus_Nzeros_Tplain']}|{triple('abs_count_minus_plain_prediction')}|")
lines+=['','## What the scan supports','']
for b in (2,4,8):
 r=[x for x in rows if int(x['B'])==b];ds=[int(x['abs_count_minus_log_prediction']) for x in r]
 lines.append(f'- B={b}: modal-count offset ranges from {min(ds)} to {max(ds)}; at m=8 it is {ds[0]}, and at m=40 it is {ds[-1]}.')
lines+=['', 'No single constant offset holds on this finite range, even with B fixed. These cells do not decide whether a bounded, threshold-dependent edge correction holds asymptotically. The 2πm substitution gives negative Q throughout the range, so it cannot itself be a dimension/count formula here. The Connes–Consani height scale should not be substituted for a finite Fourier-carrier cutoff without another argument.', '',
f"The smallest relative distance to an absolute threshold is {min(float(r['threshold_relative_margin']) for r in rows):.10g}. Negative levels outside the tested absolute bands: {max(int(r['negative_outside_abs_band']) for r in rows)}. Thus signed and absolute counts agree in these cells. Raw tiny eigenvalue signs remain numerical quantities; this does not establish a cofinal floor.", '',
'## The NOESCAPE consumer', '',
'L12 requires the signed count #{lambda<mu}≤r and a genuine r-dimensional subspace J satisfying ||A restricted to J||≤delta<mu. Its proof and the growing-rank floor route L13 remain valid. An absolute count alone misses every lambda≤−mu. Finite zero interpolation does not by itself establish the conditioned operator residual or full radicality.', '',
'Equation (5.9) is a fixed-rank package. A growing dimension-minus-zero-count proposal instead needs the growing-rank residual package (5.4); fixed-order theta-jet decay does not automatically provide it. See THEOREM_CHECK.md for exact source lines and the negative control.', '',
'## Reproduction and files', '',
'Run `uv run --with mpmath python3 scan.py 8 9 ... 40`, then `scan.py summarize`, then `validation/validate.py`, `validation/compare.py`, and `report.py`. The ellipsis means all intervening integers; scan.py accepts an explicit integer list. The shared matrix implementation is ../phase_space_V/v_forms.py; its SHA256 is recorded in each spectrum. The zero-table SHA256 is in metadata.json.', '',
'counts.csv contains all 99 threshold comparisons, signed counts, both zero counts, and margins. spectra.csv and per-cell JSON preserve every eigenvalue. validation/ contains the higher-precision replay and comparison. No source matrix or route status is changed.']
(P/'RESULT.md').write_text('\n'.join(lines)+'\n')
