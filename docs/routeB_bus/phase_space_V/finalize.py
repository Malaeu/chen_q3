"""Assemble finite K1 diagnostics; no cofinal inference."""
from pathlib import Path
import csv,json
import mpmath as mp
P=Path(__file__).resolve().parent
def csvread(n):return list(csv.DictReader((P/n).open()))
def save(n,rows):
    with (P/n).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
def main():
    mp.mp.dps=180
    baselines=[]
    for m in (8,12,16,20,24):
        b=json.loads((P/f'shake_m{m}_dps180_gl160.json').read_text())['baseline']
        baselines.append(dict(m=m,**b))
    save('literal_baselines.csv',baselines)
    a=json.loads((P/'cluster_main.json').read_text());b=json.loads((P/'cluster_validation.json').read_text())
    cc=[]
    for x,y in zip(a['levels'],b['levels']):
        cc.append(dict(i=x['i'],V_absolute_difference=mp.nstr(abs(mp.mpf(x['V'])-mp.mpf(y['V'])),100),
                       arch_absolute_difference=mp.nstr(abs(mp.mpf(x['arch'])-mp.mpf(y['arch'])),100),
                       spatial_absolute_difference=mp.nstr(abs(mp.mpf(x['spatial'])-mp.mpf(y['spatial'])),100)))
    (P/'cluster_validation_comparison.json').write_text(json.dumps(dict(main_dps=180,validation_dps=220,
        main_independent_matrix_difference=a['matrix_comparison_max'],validation_independent_matrix_difference=b['matrix_comparison_max'],levels=cc),indent=2)+'\n')
    sh=csvread('shake_summary.csv');ed=[]
    for x in sh:
        if x['convention']!='analytic_continuation':continue
        y=next(y for y in sh if y['m']==x['m'] and y['epsilon']==x['epsilon'] and y['convention']=='physical_clipped')
        ed.append(dict(m=x['m'],epsilon=x['epsilon'],V_continued_minus_clipped=mp.nstr(mp.mpf(x['V'])-mp.mpf(y['V']),100),
            lambda_continued_minus_clipped=mp.nstr(mp.mpf(x['lambda0'])-mp.mpf(y['lambda0']),100),
            w0_continued_minus_clipped=mp.nstr(mp.mpf(x['w0'])-mp.mpf(y['w0']),100),
            same_lambda_sign=x['lambda0_sign']==y['lambda0_sign']))
    save('endpoint_convention_comparison.csv',ed)
    res=csvread('resolution_main.csv');cl=csvread('cluster_main.csv')
    s='''# Phase-space V: finite K1 discriminator

**DIAGNOSTIC_NEVER_A_PROOF.**

Proshka source: f73901ce86043a9aa98c3882497a405c58c0a146, PROSHKA_VERDICT_PHASE_SPACE_V_2026-11-02.md. Exact source snapshots and Git-blob/SHA256 metadata are in source/. The diagnostics implement the owner's resolution, positive-SHAKE and excited-level tests; no source drift or cofinal V bound is claimed.

## Finding

For these finite cells, positive fixed-weight SHAKE produces markedly larger V and small theta overlap once the ground sign becomes negative. The true literal sequence stays near3.84, but its numerical value is resolution-dependent: higher-N true bottoms give about3.94–3.97 at the fixed windows tested. V changes mildly with N while the tiny eigenvalues can change by many orders of magnitude.

This is finite discrimination, not evidence of a proved divergence in broken worlds or a uniform true-world bound. V contains no prime data for a fixed function: the arithmetic enters through the recomputed minimizing vector. Positive shifts often change that vector substantially. They are not the negative-shift, nearly unchanged-shape examples in the referenced script.

Excited near-null levels already have V between5.00 and6.81. Much of the broken-world range overlaps these finite excited-state costs. Therefore a larger finite V can reflect selection of a different near-null state; it does not by itself establish spatial or frequency escape as m tends to infinity.

## Definition and normalization

For a unit real even physical vector, zero-extended outside[-L/2,L/2],

    V[f] = Apositive[f] + integral log(1+x^2)|f(x)|^2 dx,
    Apositive[f] = integral_0^infinity j(s)||f-T_s f||^2 ds,
    j(s) = exp(-s/2)/(1-exp(-2s)).

The basis is phi_n=d_n(-1)^n cos(2pi n x/L)/sqrt(L), d0=1,dn=sqrt(2). There is no x/L rescaling and no division of V by m. The archimedean matrix includes its infinite translation tail exactly through the closed constant, without truncating a frequency integral. The full even source is K=Apositive-cstar I-prime+pole*pole^T, cstar=EulerGamma+log(8pi)+pi/2. Full pole and prime powers are retained.

w0=|<f,P_N h>|^2/||P_N h||^2, with h the fixed theta profile whose transform is4xi(1/2-it). V is evaluated on the actual normalized lowest even eigenvector, not on h or a near-null surrogate. Gaps are saved; the numerical bottoms are simple. This does not certify absence of exact degeneracy by intervals.

## True literal baseline N=m

|m|lambda0|Apositive|spatial|V|w0|
|---:|---:|---:|---:|---:|---:|
'''
    for b in baselines:s+=f"|{b['m']}|{float(b['lambda0']):.7e}|{float(b['arch']):.12f}|{float(b['spatial']):.12f}|{float(b['V']):.12f}|{float(b['w0']):.10f}|\n"
    s+='''
The m8 andm16 values reproduce3.879644980139 and3.843386437630 from Proshka. The literal m20->24 increment is slightly positive, so even the true values are not strictly decreasing on these five cells.

## Fixed-window resolution

L=log(window m) stays fixed as N changes. N44..64 means44,48,52,56,60,64. The prime cutoff is determined by L, never by N.

|window m|N|lambda0|Apositive|spatial|V|w0|
|---:|---:|---:|---:|---:|---:|---:|
'''
    for r in res:s+=f"|{r['window_m']}|{r['N']}|{float(r['lambda0']):.7e}|{float(r['Apositive']):.12f}|{float(r['spatial_log1p_x2']):.12f}|{float(r['V']):.12f}|{float(r['w0']):.10f}|\n"
    s+='''
The endpoint lambda decreases are factors1.23057(log8),45.3899(log12),4.58992e8(log16), while the relative V changes are−0.001010%,+0.034014%,+0.201265%. These are not N-convergence certificates. The last log16 eigenvalue is still strongly resolution-sensitive despite the mild change in V. See resolution_ratios.csv and RESULT_resolution.md.

## Broken-world positive shifts

For every original power2^j<=m, shift its location to log(2^j)+j epsilon, while retaining weight log2/sqrt(2^j). Every other prime power, L, N, the archimedean form, the spatial form and the pole remain fixed. This is the supplied SHAKE fixed-weight control, not a fully reweighted Beurling Euler product.

The reference break_sign_keep_shape.py uses negative epsilon. Here epsilon is positive as requested. Its q formula has no support clipping; the primary rows below reproduce that formula. At m8 andm16, the endpoint2^j=m moves outside the physical correlation support. We therefore also compute q=0 for shifted locations>=L. The physical-clipped comparison is in shake_summary.csv and endpoint_convention_comparison.csv; every reported eigenvalue sign agrees between the two conventions. At the other three windows both conventions coincide.

|m|epsilon|lambda0 (sign explicit)|Apositive|spatial|V|w0|
|---:|---:|---:|---:|---:|---:|---:|
'''
    for r in sh:
        if r['convention']=='analytic_continuation':s+=f"|{r['m']}|{r['epsilon']}|{float(r['lambda0']):+.7e}|{float(r['arch']):.10f}|{float(r['spatial']):.10f}|{float(r['V']):.10f}|{float(r['w0']):.8g}|\n"
    s+='''
All four positive-shift sequences end at substantially larger V at m24 than at m8. They are not all monotone: epsilon1e−26 decreases from m8 to m12 before rising; epsilon1e−6 drops from7.505563523 at m20 to7.473311297 at m24. At epsilon1e−26 the m8/m12 bottoms remain positive; m16/m20/m24 are negative, with V5.39609/6.02528/6.57069 and w0 .14937/.01689/8.75875e−5. No finite sign observation is promoted to a broken-world asymptotic statement.

## Near-null calibration at m24

|level i|lambda_i|Apositive|spatial|V|
|---:|---:|---:|---:|---:|
'''
    for r in cl:s+=f"|{r['i']}|{float(r['lambda0_or_level']):.7e}|{float(r['arch']):.12f}|{float(r['spatial']):.12f}|{float(r['V']):.12f}|\n"
    s+='''
These seven excited eigenvalues are tiny but their V costs are appreciably above the bottom. This supports keeping the definition on exact bottoms rather than extending one numerical constant to an arbitrary near-null cluster. It is only a finite calibration.

![Phase-space V diagnostics](phase_space_V.svg)

## Checks and provenance

- Independent formula review and direct physical-integral checks are in REVIEW.md and validate_forms_independent.py. At m=N8,90dps, sampled arch/spatial/pole/correlation entries agree to roughly3e−90. The archimedean tail and physical x normalization were explicitly checked.
- Resolution:140dps/GL128 per panel, validated at log16,N64 with160dps/GL160. Absolute V change2.19e−76; relative lambda change4.75e−69. Both are precision/order checks, not interval or N-convergence certificates.
- SHAKE:180dps/GL160; m24 epsilon1e−26 and1e−6 checked at220dps/GL192. Relative eigenvalue changes are below7.54e−155.
- Cluster:180dps/GL160 and220dps/GL192, with independently built literal matrices/eigenvectors from the local-zero test. Matrix agreement, source balance, eigen residuals and V differences are saved in cluster_* files. Zero saved V differences mean agreement at the120-digit output precision, not exact equality.
- Exact source snapshots in source/ match the original Git blobs. SHA256SUMS covers delivered artifacts. Arithmetic coefficients are not refitted or omitted.

Replay from this directory using mpmath (the scripts expose their arguments). v_forms.py is the shared source of the independent archimedean/spatial forms. Run resolution.py, shake.py, cluster.py, finalize.py; plot.py additionally requires matplotlib. Individual settings and commands are in RESULT_resolution.md and RESULT_shake.md and the script entry points.

No cofinal V-bound, source drift inequality, RH conclusion, or interval certificate is claimed.
'''
    (P/'RESULT.md').write_text(s)
if __name__=='__main__':main()
