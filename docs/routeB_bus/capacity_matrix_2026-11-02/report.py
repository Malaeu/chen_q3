"""Report finite capacity spectra and zero-space mixing."""
from pathlib import Path
import json,csv,math
P=Path(__file__).resolve().parent
f=lambda x,n=8:format(float(x),f'.{n}g')
levels=list(csv.DictReader((P/'levels.csv').open()));sub=list(csv.DictReader((P/'subspaces.csv').open()));pm=list(csv.DictReader((P/'prefix_mixing.csv').open()));checks=json.loads((P/'mixing_checks.json').read_text())
lines=['# Capacity matrix check: m=16 and24','', '**DIAGNOSTIC_NEVER_A_PROOF.** Literal even CCM, N=m and L=ln m. Arithmetic180dps. Source branch at start: rh_clean @9c6fa2a8032f5ab78993b8c1784ea122f22cd4a0.', '',
'## Matrices and normalization','',
'Use the unit physical basis ψ_n(x)=d_n(−1)^n cos(2πnx/L)/sqrt(L) on |x|≤L/2 and zero outside; d_0=1,d_n=sqrt(2) for n>0. For every positive zeta ordinate γ_k≤400,', '',
'`E_kn = ψ̂_n(γ_k) = 2 d_n γ_k sin(γ_k L/2) / [sqrt(L)(γ_k²−(2πn/L)²)]`.', '',
'This is the exact analytic rational-times-sine formula evaluated at high-precision ordinates, with a direct sinc removable extension. Rows are unweighted: there is no local normalization, H division, or2π divisor. Define G=E*E and C=EE*. Both matrices were built at180dps. There are202 positive-zero rows, and carrier dimensions17 and25.', '',
'The source explicit formula counts both ±γ. Thus **2G**, not G, is the retained-critical-zero contribution to the full Weil matrix A. Raw G eigenvalues are also retained. Both pole sectors already belong to A; no extra pole term is added to2G. See [NORMALIZATION.md](NORMALIZATION.md) for source lines.', '',
'C has compulsory nullity at least185/177; all17/25 eigenvalues of G are numerically resolved positive at the final cutoff, so the computed nonzero C spectrum is exactly the G spectrum via W_i=EU_i/sqrt(g_i). These large C nullspaces live in zero-index space; they are not extra physical near-null modes. The physical cluster consists of small but resolved positive G eigenvalues.', '',
'## Spectrum and carrier eigenvectors','',
'The capacity Gram reproduces the cluster counts and almost the same carrier eigenbasis, but not yet the small eigenvalues quantitatively. Every best-overlap pairing between G and A has the same index.', '',
'|m|2g₀(400)/λ₀(A)|2g_top(400)/λ_top(A)|Minimum same-index overlap²|‖A−2G‖op|Relative to ‖A‖op|',
'|---:|---:|---:|---:|---:|---:|']
data={m:json.loads((P/f'cell_m{m}.json').read_text()) for m in (16,24)}
for m in (16,24):
 r=data[m];ls=[x for x in levels if int(x['m'])==m];op=float(r['A_minus_2G_operator_norm']);an=float(r['A_eigenvalues'][-1])
 lines.append(f"|{m}|{f(ls[0]['twice_G_over_A'])}|{f(ls[-1]['twice_G_over_A'])}|{f(min(float(x['same_index_carrier_overlap_squared']) for x in ls))}|{f(op)}|{f(op/an)}|")
lines+=['', '|m|B|Cluster count of A / raw G / 2G|Largest A-vs-2G cluster principal angle|', '|---:|---:|:---|---:|']
for r in sub:
 raw=data[int(r['m'])]['prefixes'][-1][f"G_count_B{r['B']}"]
 lines.append(f"|{r['m']}|{r['B']}|{r['A_cluster_count']} / {raw} / {r['twice_G_cluster_count']}|{f(r['maximum_principal_angle_degrees'],6)}°|")
lines+=['', '![Spectrum and prefix convergence](spectrum_convergence.svg)', '',
'## Convergence as zeros are added','',
'Fifty prefix sizes are retained in spectra.csv. Each Gram update is a positive rank-one addition. Prefixes with q<d have structural nullity at least d−q; their near-zero floating values are labelled accordingly. The following table uses400 only as the final finite reference, not as the infinite-zero limit. Relative errors of the deepest levels remain large even between350 and400.', '',
'|m|q|Last γ retained|2g₀(q)/λ₀(A)|2g_top(q)/λ_top(A)|Worst relative eigenvalue change from q to202|', '|---:|---:|---:|---:|---:|---:|']
for m in (16,24):
 r=data[m]
 for p in r['prefixes']:
  if 'U' not in p:continue
  lines.append(f"|{m}|{p['q']}|{f(p['height'],7)}|{f(2*float(p['g_eigenvalues'][0])/float(r['A_eigenvalues'][0]),7)}|{f(2*float(p['g_eigenvalues'][-1])/float(r['A_eigenvalues'][-1]),7)}|{f(max(float(x) for x in p['relative_eigenvalue_difference_from_full']),6)}|")
lines+=['', 'The final residual is numerically almost rank one and almost parallel to the endpoint-evaluation direction b=(1,sqrt(2),…,sqrt(2)), since ψ_n(L/2)=d_n/sqrt(L). This is a measured finite-matrix observation, not an unconditional infinite-zero tail bound.', '',
'|m|Second/largest eigenvalue of A−2G|Top residual direction overlap² with b|', '|---:|---:|---:|']
for r in checks:lines.append(f"|{r['m']}|{f(r['tail_second_over_first'])}|{f(r['tail_top_boundary_overlap_squared'],12)}|")
lines+=['', 'All computed residual eigenvalues are positive, but their positivity is not certified by these floating computations. Off-critical zero contributions cannot be deleted: interpreting A−2G as an exclusively positive real-zero tail would require an additional premise. No extrapolated tail or completed convergence claim is made.', '',
'## Mixing between zeros','',
'The nonzero C eigenvectors are W=EU diag(g^(−1/2)), with unit columns. Their weights |W_ki|² describe mixing in zero-index space. N_eff=1/sum_k|W_ki|⁴ measures participation. Full signed components, top-five weights and shortest contiguous index windows carrying90% mass are saved.', '',
'Large lifted modes mix several of the first zeros, rather than belonging to one zero each. Examples: at m16, mode i14 has its largest weights at zeros1 and2; at m24, mode i20 is shared mainly among zeros2,3,1. The lowest cluster modes instead use broad sets of higher zeros; their left eigenvectors remain sensitive to increasing the height cutoff even while their carrier eigenvectors are close to those of A.', '',
'For example, extending height300 to400 gives bottom carrier-vector overlap²0.999999929 (m16) /0.999999839 (m24), but only0.791896 /0.574713 for the zero-space C eigenvectors after zero-padding the shorter vector. Stable carrier geometry therefore does not mean that its zero-index mass or smallest energy has converged. The exact finite comparison used is |<W_i,Wq_i>|²=|<U_i,Uq_i>|² gq_i/g_i.', '',
'Adjacent normalized evaluation-row correlations also distinguish the low-band and exterior regions. These are |C_j,j+1|/sqrt(C_jj C_j+1,j+1), not eigenvector weights:', '',
'|m|Median adjacent correlation below2πm/L|Median above2πm/L|Median with both heights>200|', '|---:|---:|---:|---:|']
for r in checks:
 c=r['adjacent_row_correlation'];lines.append(f"|{r['m']}|{f(c['below']['median'])}|{f(c['above']['median'],12)}|{f(c['above200']['median'],12)}|")
lines+=['', 'High-frequency evaluation rows are almost collinear. The rational formula displays the reason: its leading large-t vector is proportional to b=(d_n), with scalar2 sin(tL/2)/(sqrt(L)t). Thus many high zeros add to a nearly common boundary direction; they do not act as orthogonal independent coordinates.', '',
'![Zero-space eigenvectors and normalized kernel](zero_mixing.svg)', '',
'## Every level at height400','',
'C uses the raw G eigenvalues below; multiplication by2 is only for comparison with A. Indices i are zero-based; zero indices k are one-based. The last column lists the three largest zero-space weights, not a one-to-one matching.', '']
for m in (16,24):
 lines += [f'### m={m}', '', '|i|λ_i(A)|g_i(E*E)|2g_i/λ_i|Carrier overlap²|N_eff|Top zero indices: weights|', '|---:|---:|---:|---:|---:|---:|:---|']
 for r in levels:
  if int(r['m'])!=m:continue
  kk=r['top_five_zero_indices'].split(',');ww=r['top_five_weights'].split(',');top=', '.join(f'{k}: {float(w):.3f}' for k,w in zip(kk[:3],ww[:3]))
  lines.append(f"|{r['i']}|{f(r['A_eigenvalue'],7)}|{f(r['G_eigenvalue'],7)}|{f(r['twice_G_over_A'],7)}|{f(r['same_index_carrier_overlap_squared'],8)}|{f(r['zero_participation'],5)}|{top}|")
 lines+=['']
lines+=['## Checks, files and reproduction','',
'The202 ordinates through400 were obtained with mpmath.zetazero at180dps; the first zero above400 is also saved. The inherited table through300 is hash-pinned. Rational Fourier evaluations were independently checked against sinc at every row and mode (maximum difference1.11e−178), and against physical eight-panel GL128 integration at first/last/nearest-modal cases (maximum difference2.30e−164). See RESULT_validation.md.', '',
'The direct C eigensystem checks use CW−W diag(g), W*W−I, and trace(C)−trace(G). Maximum absolute residuals are1.13e−154,1.53e−128 and7.72e−180 respectively. No float64 eigensolver is used. Float conversion is confined to plotting and descriptive participation/weight-window statistics. Full C is constructed in mixing.py and stored implicitly without loss through its180-digit E factor; nearby entries are exported in nearby_kernel.csv.', '',
'cell_m16.json/cell_m24.json store E,G,A and both carrier eigenbases, the zero-space W, residual spectra,50 prefix spectra and selected prefix eigenvectors. spectra.csv and convergence.csv preserve prefix data. levels.csv, zero_components.csv, nearby_kernel.csv, subspaces.csv and prefix_mixing.csv preserve all comparisons. NORMALIZATION.md identifies the exact source conventions.', '',
'Replay: `zeros.py`; `validation.py`; `capacity.py 16`; `capacity.py 24`; `capacity.py aggregate`; `mixing.py`; `plot.py`; `report.py`. Dependencies: mpmath,numpy,matplotlib (validation uses its documented mpmath quadrature). Source A files are the existing pinned180dps/GL160 eigensystems. The zero-table and source-byte hashes are recorded.', '',
'**Outcome:** capacity eigenmodes closely reproduce the carrier modes and cluster counts, while the finite height400 truncation still misses a substantial relative part of the smallest energies. The zero-space modes exhibit mixing, not a single-zero energy ladder. This is a finite diagnostic, not a source upper bound, RH result, or cofinal counting theorem.']
(P/'RESULT.md').write_text('\n'.join(lines)+'\n')
