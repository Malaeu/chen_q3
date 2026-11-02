"""Render per-level nearest-root tables and bounded conclusions."""
from pathlib import Path
import csv,json,collections
P=Path(__file__).resolve().parent
rows=list(csv.DictReader((P/'matches.csv').open()))
summ=list(csv.DictReader((P/'matching_summary.csv').open()))
collapse=list(csv.DictReader((P/'collapse.csv').open()))
f=lambda x,n=8:format(float(x),f'.{n}g')
lines=['# Level–zero ladder: repository reuse and missing higher-level test','',
'**DIAGNOSTIC_NEVER_A_PROOF.** Source rh_clean @ a412a678a4ae1df4f03106d1a46cf5453451c65a. Literal even CCM, N=m, L=ln m, unit physical eigenvectors.', '',
'## Repository search came first','',
'The repository already contains ground-transform root searches at m=13,23,43 (`phase5_codex/xi_row_zeros.py`). Their archived polynomial-root displacement table has a documented ERRATUM; it is not reused as numerical evidence. Recent `ladder_limit/identify` and `zero_height_local` supply physical Fourier formulas, accurate zeta ordinates and full m16/m24 eigenpairs. The missing experiment is the lifted-level association, not the invention of ground-root tracking. See [PREVIOUS_WORK.md](PREVIOUS_WORK.md) for pinned blobs and corrections.', '',
'The CCM source-paper theorem concerns zeros of a ground-vector transform as eigenvalues of a perturbed scaling operator. Those are not the energy eigenvalues of the Weil matrix K plotted here.', '',
'## Definitions and reproducibility','',
'Main cluster convention: |lambda_i|<m^(-2). Sensitivity runs use B=4 and8. Remaining positive eigenvalues are sorted increasingly; j=1 is the first level above the threshold and is assigned gamma_1. Indices i are zero-based. No zeros are skipped in this ordinal convention. Every level above m^(-8) is included in the root scan, so both alternative thresholds are covered.', '',
'The physical basis is d_n(-1)^n cos(2πnx/L)/sqrt(L), d_0=1, d_n=sqrt(2) for n>0, zero outside the window. Its direct sinc Fourier transform is evaluated with removable modal values. Away from those points:', '',
'`Phi_i(t) = 2 t sin(tL/2)/sqrt(L) * sum_n d_n v_ni / (t²-(2πn/L)²)`.', '',
'Roots of a rational numerator with 100-digit rounded coefficients seed exact rational real-root isolation; each positive candidate is then refined and evaluated with the direct sinc transform. At modes n≤N the expression is removable, not automatically zero. At n>N, t=2πn/L is an exact structural zero for every carrier vector. Those common roots are retained and flagged; they are not evidence of zeta identification.', '',
'm16/m24 reuse 180 dps/GL160 eigensystems; m32 uses160dps/GL128; m40 roots use180dps/GL160, compared with160dps/GL128. All original matrix terms and prime powers remain. There are67 profiles and4,018 retained positive roots, including the exterior lattice through120 and the next two lattice points. All positive off-lattice roots of the rounded numerator were considered, including those beyond120; this range covers the first23 matched zeta ordinates. Searches are finite numerical diagnostics, not root enclosures for exact CCM eigenvectors.', '',
'## Does the scaled energy curve collapse?','',
'Define Ω_m=2πm/ln m and x=gamma_j/Ω_m; all logarithms in the energy plots are natural. There is a qualitatively similar upper branch for B=2, but no tight threshold-independent collapse. The shoulder moves with m and with the cluster threshold. The table quantifies linearly interpolated **ln lambda** curves on their common x interval; factors are exp(max ln lambda − min ln lambda) across the four carriers. No extrapolation is used.', '',
'|B|Common x range|Median lambda factor|Maximum lambda factor|Median / max factor on 0.6≤x≤1|',
'|---:|:---|---:|---:|:---|']
for r in collapse:
 lines.append(f"|{r['B']}|{f(r['x_common_min'],5)}–{f(r['x_common_max'],5)}|{f(r['median_lambda_factor'],5)}|{f(r['max_lambda_factor'],6)}|{f(r['bulk_median_lambda_factor'],5)} / {f(r['bulk_max_lambda_factor'],5)}|")
lines+=['', '![Energy curves and nearest-root distances](level_zero_ladder.svg)', '',
'As a modest check of m-dependence, `simple_models.json` fits ln lambda=a+b x+c x², and then adds d ln m. For B=2 the mean leave-one-carrier-out log RMSE improves only from0.713 to0.668. These are descriptive fits, not an inferred F or an asymptotic law. An unrestricted F(x,m) could interpolate any finite table; this experiment does not identify one.', '',
'## Does Fourier-root matching select the ordinal ladder?','',
'For each gamma_j and each lifted vector, the cost is distance to its nearest positive real Fourier root divided by the smaller adjacent zeta spacing (first zero uses its next gap). Three conventions are saved:', '',
'- **ordinal:** j-th increasing energy gets gamma_j, without optimization.',
'- **root_independent:** each gamma independently picks the lowest-cost vector; repetition is allowed.',
'- **root_bijective:** Hungarian minimum-total-cost assignment forces distinct vectors. This is a fitted matching, not independent evidence for the ordinal hypothesis. Exterior-lattice ties have no intrinsic vector identification; tie-breaking is incidental.', '',
'|m|Lifted levels (B=2)|Ordinal median root distance / spacing|Bijective median distance / spacing|Bijective pairs retaining ordinal index|Distinct levels used by independent match|',
'|---:|---:|---:|---:|:---|---:|']
for m in (16,24,32,40):
 a={r['method']:r for r in summ if r['B']=='2' and int(r['m'])==m};o=a['ordinal'];b=a['root_bijective'];u=a['root_independent']
 lines.append(f"|{m}|{o['lifted_count']}|{f(o['median_spacing_distance'],5)}|{f(b['median_spacing_distance'],5)}|{b['ordinal_agreements']}/{b['lifted_count']}|{u['distinct_levels_used']}|")
lines+=['', 'The ordinal errors are typically about half a local zeta spacing. The optimized bijection substantially reorders the levels. The independent choice is many-to-one: at m24,10/11 zeros select i14; at m32,14/15 select i18; at m40,17/19 select i22. A single low lifted vector retains many nearby zeta zeros. This does not support one distinct lifted energy level per zeta ordinate.', '',
'![All-pairs root matching costs](root_matching_costs.svg)', '',
'![Energy curves under alternative assignments](alternative_assignments.svg)', '',
'## Every lifted level: main B=2 ordinal assignment','',
'Nearest-root positions and signed offsets are computed before conversion to display precision. Full100-digit values, x and ln lambda are in matches.csv; all B=4/8 rows and both alternative assignments are there too. An asterisk marks a common exterior-modal root.', '']
for m in (16,24,32,40):
 lines+= [f'### m={m}', '', '|i|j|lambda_i|gamma_j|Nearest real Fourier zero|root−gamma_j|', '|---:|---:|---:|---:|---:|---:|']
 for r in rows:
  if int(r['m'])!=m or r['B']!='2' or r['method']!='ordinal':continue
  mark=' *' if r['root_kind']=='structural_exterior' else ''
  lines.append(f"|{r['i']}|{r['j']}|{f(r['lambda_i'],10)}|{f(r['gamma'],11)}|{f(r['nearest_real_fourier_zero'],11)}{mark}|{f(r['signed_zero_offset'],9)}|")
 lines+=['']
lines+=['## Validation and limits','',
'No sign-change bracket on the independent step0.05 physical-frequency scan was unmatched. The maximum internal direct-sinc root residual is1.98e−160. Roots are serialized to125 significant digits; the largest serialized position residual |Phi/Phi′| is4.98e−123. All737 m40 off-lattice roots were refined again with independent160-digit eigenvectors; maximum location difference is4.97e−123, at serialization scale. These figures validate computed finite roots, not exact source intervals or a cofinal correspondence. Root counts for the rounded polynomial include negative and nonreal squared-frequency roots; excited vectors are not assumed real-rooted.', '',
'`root_method.md`, `root_summary.json`, per-carrier root checks and `root_validation_m40.json` retain the details. The first-order |Phi/Phi′| quantity is a numerical position residual, not a rigorous enclosure radius.', '',
'Files: matches.csv (all per-level assignments), matching_costs.csv (full pairwise costs), matching_summary.csv, collapse.csv, simple_models.json, roots.csv, full eigensystems, code, source hashes and plots. Reproduce with eigenpairs.py; roots.py per source cell; root_counts.py; root_finalize.py; root_serialized.py; matching.py; plot.py; report.py. Dependencies: mpmath, sympy, numpy, scipy, matplotlib. See the script entry points for exact per-cell arguments.', '',
'**Conclusion:** the requested ordinal ladder is not supported by the Fourier-root matches. A rough B=2 upper-branch energy similarity survives, while the threshold shoulder and higher-threshold comparisons vary substantially. This leaves no identified universal F(x,m), and supplies no RH or NOESCAPE theorem input.']
(P/'RESULT.md').write_text('\n'.join(lines)+'\n')
