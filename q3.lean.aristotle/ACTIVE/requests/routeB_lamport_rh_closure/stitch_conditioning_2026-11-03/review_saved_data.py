"""Read-only consistency review of completed checkpoints; no new eigenproblems."""
from pathlib import Path
from collections import Counter
import hashlib,json
import mpmath as mp
P=Path(__file__).resolve().parent
def main():
    mp.mp.dps=120
    source=json.loads((P/'INPUTS.json').read_text())
    for s in source['sources']:
        b=(P/'inputs'/s['name']).read_bytes()
        assert hashlib.sha256(b).hexdigest()==s['sha256']
        assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==s['git_blob']
    bs=list((P/'B_stitch').glob('cell_*_dps100.json'));assert len(bs)==36
    max_partition=mp.mpf(0)
    for f in bs:
        z=json.loads(f.read_text());r=z['metrics'];s=z['section']
        for coord in [s['section0'],s['section2'],z['quiet_schur0'],z['quiet_schur2']]:
            assert coord['inertia_identity']
            assert coord['full']['negative']==coord['eliminated']['negative']+coord['schur']['negative']
        a=mp.mpf(r['projection_quiet_norm']);b=mp.mpf(r['projection_complement_norm']);n=mp.mpf(r['full_f_norm'])
        max_partition=max(max_partition,abs(a*a+b*b-n*n)/max(1,n*n))
        if s['old_negative_index']:
            assert s['section_interpretation']=='STATIONARY_ALGEBRAIC_INF_MINUS_INFINITY'
    assert max_partition<mp.mpf('1e-80')
    cells=[json.loads(f.read_text()) for f in (P/'C_conditioning/cells').glob('*_m*.json')]
    expected={(w,m) for w in ['zeta','dh','plant'] for m in range(16,121)}
    assert {(c['world'],c['m']) for c in cells}==expected and len(cells)==315
    status=Counter();rows=0
    for c in cells:
        f=P/'C_conditioning/matrices'/f"cell_{c['world']}_m{c['m']}.npz"
        assert hashlib.sha256(f.read_bytes()).hexdigest()==c['source_matrix_sha256']
        assert len([r for r in c['rows'] if r['variant']=='base'])==3
        assert all(r.get('sigma_min') is not None and mp.mpf(r['sigma_min'])>0 for r in c['rows'] if r['variant']=='base')
        assert all(r.get('lambda_r_preferred') is not None for r in c['rows'])
        for r in c['rows']:
            rows+=1;status[r['Schur_status']]+=1
            assert r['r']==max(0,r['dimension']-r['q'])
            assert r['quiet_coupling_retained']
            if r['Schur_status']=='NUMERIC_IDENTITY_PASS':
                assert r['N_A2']-r['r']==r['eliminated_negative_index']+r['S_negative_index']-r['r']
            assert r['Schur_status']!='MISMATCH'
    lookup={(c['world'],c['m']):c for c in cells};pair=Counter()
    for m in range(16,121):
        z={(r['cut'],r['variant']):r for r in lookup['zeta',m]['rows']}
        w={(r['cut'],r['variant']):r for r in lookup['plant',m]['rows']}
        for key in z.keys() & w.keys():
            a,b=z[key],w[key]
            assert not(a['N_A2_unresolved'] or b['N_A2_unresolved'])
            pair[str((b['count_minus_r']-a['count_minus_r'],b['N_A2']-a['N_A2'],b['r']-a['r']))]+=1
    result=dict(status='SAVED_DATA_CONSISTENCY_REVIEW_PASS',scope='No new eigensolve; not an interval certificate or independent proof of source analysis.',B_cells=len(bs),B_max_relative_projection_partition_error=mp.nstr(max_partition,30),C_cells=len(cells),C_resolved_base_sigma=3*len(cells),C_lambda_r_resolved_rows=rows,C_all_cutoff_rows=rows,C_Schur_status=dict(status),paired_planted_index_difference_counts=dict(pair),source_hashes_checked=len(source['sources']),route_state_changed=False)
    (P/'REVIEW.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
