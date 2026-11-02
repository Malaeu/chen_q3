"""Assemble V-level expectation gaps, without an operator-gap claim."""
from pathlib import Path
import csv,json
import mpmath as mp
P=Path(__file__).resolve().parent
def save(n,rows):
    with (P/n).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
def main():
    mp.mp.dps=160;cells=[]
    for tag,m in [('literal',12),('literal',16),('literal',20),('literal',24),('literal',32),('resolution',8),('resolution',12)]:
        cells+=json.loads((P/f'{tag}_window{m}.json').read_text())
    assert len(cells)==13
    summary=[x['summary'] for x in cells];levels=[];first8=[]
    for c in cells:
        s=c['summary'];r=dict(window_m=s['window_m'],N=s['N'],literal=s['literal'])
        for l in c['levels']:
            levels.append(dict(window_m=s['window_m'],N=s['N'],literal=s['literal'],**l))
            if l['i']<8:r[f'V{l["i"]}']=l['V']
        first8.append(r)
    save('summary.csv',summary);save('first_eight_V.csv',first8);save('all_levels.csv',levels)
    validation=[]
    for m,N in [(32,32),(12,68)]:
        lo=next(c for c in cells if c['summary']['window_m']==m and c['summary']['N']==N)
        hi=json.loads((P/f'validation_window{m}.json').read_text())[0]
        diffs={k:mp.nstr(abs(mp.mpf(lo['summary'][k])-mp.mpf(hi['summary'][k])),100) for k in
               ('V0','V1','gap_V1_minus_V0','cluster_min_gap','all_even_min_gap','projected_h_V','projected_h_V_minus_V0')}
        validation.append(dict(window_m=m,N=N,main_dps=160,validation_dps=180,main_order=128,validation_order=160,
            absolute_differences=diffs,max_first8_V_difference=mp.nstr(max(abs(mp.mpf(lo['levels'][i]['V'])-mp.mpf(hi['levels'][i]['V'])) for i in range(8)),100),
            same_cluster_min_index=lo['summary']['cluster_min_index']==hi['summary']['cluster_min_index'],
            same_all_even_min_index=lo['summary']['all_even_min_index']==hi['summary']['all_even_min_index'],
            saved_significant_digits=100,zero_means_agreement_at_saved_precision=True))
    (P/'validation.json').write_text(json.dumps(validation,indent=2)+'\n')
    text='''# V-gap stability and unheated theta reference

**DIAGNOSTIC_NEVER_A_PROOF.**

The functional and physical conventions are exactly those in ../v_forms.py and ../RESULT.md. This follow-up recomputes even eigenvectors at160dps, GL128 per each of eight panels; m32 and log12,N68 are replayed at180dps/GL160. The source includes the full archimedean tail, all active prime powers and the pole. Fixed-window N varies independently of L and the prime cutoff.

We report V_i=<f_i,B_V f_i> for the normalized eigenvectors of the CCM matrix K, in ascending K-eigenvalue order. g=V_1−V_0 is an expectation-value gap, not an eigenvalue gap of B_V. Two minima are reported: over the requested cluster i=1..7, and over all excited even levels i=1..N. Neither is an infimum over arbitrary linear combinations orthogonal to f_0.

## Gaps and projected unheated h

Here h_N=P_Nh/||P_Nh||, with hat h=4xi(1/2-it); no heat evolution is applied. In literal rows N=m. In fixed-window rows L=log(window m).

|window m|N|V0|V1−V0|min1..7 gap|min1..N gap|V[h_N]|V[h_N]−V0|
|---:|---:|---:|---:|---:|---:|---:|---:|
'''
    for s in summary:text+='|'+str(s['window_m'])+'|'+str(s['N'])+'|'+'|'.join(f"{float(s[k]):.12f}" for k in ['V0','gap_V1_minus_V0','cluster_min_gap','all_even_min_gap','projected_h_V','projected_h_V_minus_V0'])+'|\n'
    text+='\nAll minima in this finite scan occur at i=1. The complete all-level expectations are preserved in all_levels.csv.\n\n## First eight levels\n\n|window m|N|'+ '|'.join('V'+str(i) for i in range(8))+'|\n|---:|---:|'+ '|'.join(['---:']*8)+'|\n'
    for r in first8:text+='|'+str(r['window_m'])+'|'+str(r['N'])+'|'+'|'.join(f"{float(r['V'+str(i)]):.10f}" for i in range(8))+'|\n'
    lits=[s for s in summary if s['literal']];ress=[s for s in summary if not s['literal']]
    interval=lambda rr:(min(float(s['gap_V1_minus_V0']) for s in rr),max(float(s['gap_V1_minus_V0']) for s in rr))
    text+=f'''\n## Interpretation

The literal gaps range from{interval(lits)[0]:.9f} to{interval(lits)[1]:.9f}; the fixed-window gaps range from{interval(ress)[0]:.9f} to{interval(ress)[1]:.9f}. Thus the sampled gaps are of order one and remain positive, but the value is not exactly1 or resolution-invariant. These13finite cells do not establish a uniform cofinal lower bound.

The projected-h value is almost constant around3.90744055. It exceeds V0 on the literal cells, and is smaller than V0 on the high-resolution fixed-window cells. This is compatible with the CCM ground minimizing K rather than V. Positive diagonal expectation gaps do not make f0 a minimizer of V or establish coercivity of V on f0-perpendicular space: B_V has off-diagonal entries in the K-eigenbasis. Their largest magnitude is retained in summary.csv.

The label high resolution is not a claim of N-convergence. The corresponding lambda0 and lambda1, eigen residuals and w0 are recorded in summary.csv; stabilization of V expectations does not certify convergence of tiny K-eigenvalues.

## Reproduction and checks

gap.py builds each requested window at its largest N, then diagonalizes the principal submatrices. It records all even V expectations, first-eight eigenvectors and normalized h coefficients. source_v_forms_sha256 pins the unchanged shared implementation in every raw cell. validation.json compares both higher-precision replays and verifies the minimizer indices; zero saved differences mean agreement at100significant output digits, not exact equality.

Example runs:

```sh
uv run --with mpmath python3 gap.py --window 32 --N 32 --tag literal
uv run --with mpmath python3 gap.py --window 8 --N 56 60 64 68 --tag resolution
uv run --with mpmath python3 gap.py --window 12 --N 56 60 64 68 --tag resolution
uv run --with mpmath python3 gap.py --window 32 --N 32 --dps 180 --order 160 --tag validation
uv run --with mpmath python3 gap.py --window 12 --N 68 --dps 180 --order 160 --tag validation
uv run --with mpmath python3 finalize.py
```

For the other literal rows repeat the first command with m=N=12,16,20,24. No interval, NOESCAPE, RH or uniform-gap theorem is claimed.
'''
    (P/'RESULT.md').write_text(text)
    print(json.dumps(validation,indent=2))
if __name__=='__main__':main()
