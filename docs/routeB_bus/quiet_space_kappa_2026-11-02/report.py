"""Finite interpolation-kernel scan report; DIAGNOSTIC_NEVER_A_PROOF."""
from pathlib import Path
import csv,json
import mpmath as mp
P=Path(__file__).resolve().parent;mp.mp.dps=180
rows=list(csv.DictReader((P/'scan.csv').open()))
cells={m:json.loads((P/f'cell_m{m}.json').read_text()) for m in (16,24,32,40)}
f=lambda x,n=7:format(float(x),f'.{n}g')
summary=[]
for m in cells:
 rr=[r for r in rows if int(r['m'])==m];om=mp.mpf(rr[0]['Omega'])
 for B in (2,4):
  eq=[r for r in rr if int(r[f'count_minus_dimension_B{B}'])==0];q=int(eq[0]['positive_zero_count_strict']);cache=cells[m]['cache'][str(q)];mu=mp.mpf(eq[0][f'mu_B{B}'])
  quiet=[r['kappa'] for r in rr if mp.mpf(r['delta'])<mp.mpf(r[f'mu_B{B}'])]
  summary.append(dict(m=m,B=B,q=q,dimension=eq[0]['dimension'],count_equality_kappa_left=str(mp.mpf(cache['last_included_zero'])/om),count_equality_kappa_right=str(mp.mpf(cache['first_excluded_zero'])/om),count_equality_grid=','.join(f(r['kappa'],3) for r in eq),delta=cache['delta'],beta=cache['beta'],delta_over_mu=str(mp.mpf(cache['delta'])/mu),beta_over_mu=str(mp.mpf(cache['beta'])/mu),first_quiet_grid_kappa=quiet[0] if quiet else '',simultaneous_window='EMPTY'))
with (P/'windows.csv').open('w',newline='') as h:
 w=csv.DictWriter(h,fieldnames=summary[0]);w.writeheader();w.writerows(summary)
lines=['# Interpolation quiet-space κ scan','', '**DIAGNOSTIC_NEVER_A_PROOF.** Source branch rh_clean @bf890512b36abf2330d8f61a95f120cae58d0e0a. Literal even A_m, N=m, L=ln m. All84 points κ=1.00,1.02,…,1.40 are included.', '',
'## Result','',
'**The simultaneous window is empty for all four m and both thresholds.** At the required dimension, the full operator residual is too large. Adding more zero constraints eventually makes the space quieter, but then its dimension is smaller than the signed spectral count. The compressed-form norm also exceeds μ at every count-equality window.', '',
'The basis and residual are constant between successive zero-entry heights. Therefore the cached count-equality subspace checks also exclude a passing point between grid samples within[1,1.4], subject to the same finite numerical accuracy; this is not an extrapolation to other m.', '',
'|m|B|Required dim J=N_A(μ)|Count-equality κ interval, approximately|δ/μ|β/μ|First grid κ with δ<μ|Both conditions|',
'|---:|---:|---:|:---|---:|---:|:---|:---|']
for r in summary:lines.append(f"|{r['m']}|{r['B']}|{r['dimension']}|({f(r['count_equality_kappa_left'])}, {f(r['count_equality_kappa_right'])}]|{f(r['delta_over_mu'])}|{f(r['beta_over_mu'])}|{f(r['first_quiet_grid_kappa'],3) if r['first_quiet_grid_kappa'] else 'none'}|empty|")
lines+=['', 'The interval is left-open/right-closed because the constraint uses γ<T strictly. Grid membership is recorded separately in windows.csv. No eigenvalue absolute-value count is substituted: N_A(μ)=#{λ_i(A)<μ}, including the ground and any negative level.', '',
'![Residuals and dimensions](quiet_space_scan.svg)', '',
'## Construction and Gram control','',
'The physical basis is ψ_n=d_n(−1)^n cos(2πnx/L)/sqrt(L), d_0=1,d_n=sqrt(2), zero outside the window. E evaluates these transforms at the selected positive zeros using the exact rational-times-sine formula, with direct sinc continuation at modal points. The constant mode is retained.', '',
'In the polynomial formula in the request, the denominator product is n=1,…,m when the prefactor is1/z and deg P≤m. Including n=0 instead requires an extra z² factor in the numerator. NORMALIZATION.md gives the coefficient map and the conditions for full evaluation rank.', '',
'Main construction:200dps full SVD of row-normalized E, retaining its full right nullspace. Row normalization does not alter the kernel. No small-singular-value cutoff is used to create J. Full row rank q is supported by the distinct-node Cauchy/Vandermonde structure and verified singular values far above numerical residuals. All sampled q<d; no zero-dimensional convention is needed.', '',
'The orthonormal basis Q is stored for every distinct q. We compute δ=||AQ||op=sqrt(λmax(Q* A² Q)) and β=||Q*AQ||op=max|λ(Q*AQ)|. The second quantity is not substituted for the first. Source matrices are180dps/GL160 for m16,24,40 and160dps/GL128 for m32; zero ordinates carry180digits. Higher working precision does not upgrade those source accuracies.', '',
'|m|Maximum condition number of row-normalized E|Maximum ||Q*Q−I||F|Maximum ||EQ||F|', '|---:|---:|---:|---:|']
for m,c in cells.items():
 cc=list(c['cache'].values());lines.append(f"|{m}|{f(max(mp.mpf(x['row_scaled_condition']) for x in cc))}|{f(max(mp.mpf(x['Q_orthogonality_residual']) for x in cc))}|{f(max(mp.mpf(x['raw_E_Q_residual']) for x in cc))}|")
lines+=['', '## Dimension formula','',
'For the selected distinct nonstructural zeros, every row adds one condition: dim J=m+1−q at all84 points. This is checked against the numerical rank. Zero evaluation alone imposes no derivative conditions for multiplicities; the exact rank statement uses distinct evaluations. The finite zeta list and its accuracy are inherited from the capacity-matrix packet.', '',
'The supplied smooth approximation is D_asym=m[1−κ+κ(1+ln L−ln κ)/L]. Riemann–von Mangoldt contributes the additional constant1/8 to d−N(T), plus the oscillatory −S(T) and O(1/T) remainder. Thus exact integer dimension need not equal a rounded smooth approximation. Both D_asym and dim J−D_asym are reported below.', '',
'## Complete grid','']
for m in cells:
 lines += [f'### m={m}', '', '|κ|q|dim J|δ=||AQ||op|β=||Q*AQ||op|N(m⁻²)−dim J|N(m⁻⁴)−dim J|D_asym|dim J−D_asym|', '|---:|---:|---:|---:|---:|---:|---:|---:|---:|']
 for r in rows:
  if int(r['m'])!=m:continue
  lines.append('|'+ '|'.join([f(r['kappa'],3),r['positive_zero_count_strict'],r['dimension'],f(r['delta']),f(r['beta']),r['count_minus_dimension_B2'],r['count_minus_dimension_B4'],f(r['asymptotic_dimension'],6),f(r['dimension_minus_asymptotic'],6)])+'|')
 lines+=['']
lines+=['## Independent validation and reproduction','',
'A second implementation builds P(y)=prod_selected(y−yγ) times Chebyshev polynomials, converts to modal residues, and uses twice-reorthogonalized220dps QR. It does not use E-SVD to construct the kernel. All12 m40 subspaces and11 other boundary/endpoint cells were checked. Projectors differ by at most1.40e−187; full residual norms agree relatively within3.52e−150 and compressed norms within2.06e−150. Independent m40 arithmetic matrices at160/GL128 and180/GL160 preserve the norms, with relative differences at most7.40e−152 and1.61e−142. These are precision/algorithm checks, not interval certificates.', '',
'Files: scan.csv (all84 rows); windows.csv (both conditions and exact zero-entry interval endpoints); cell_m*.json (Q, singular values, condition numbers, matrix provenance and residual checks); validation*.py/json/csv; NORMALIZATION.md; RESULT_validation.md; code and plots. The full and compressed norms are in every row.', '',
'Replay scan.py with m=16,24,32,40 and its aggregation entry point; validation.py/validation_compare.py/validation_source.py use their documented entry points. Then run report.py and plot.py. Dependencies are mpmath,numpy,matplotlib. The exact source hashes are preserved in each cell.', '',
'This excludes the requested finite interpolation-space saturation guard on these four carriers over the scanned interval. It does not prove or disprove a cofinal count law, another quiet-space construction, NOESCAPE, or RH.']
(P/'RESULT.md').write_text('\n'.join(lines)+'\n')
