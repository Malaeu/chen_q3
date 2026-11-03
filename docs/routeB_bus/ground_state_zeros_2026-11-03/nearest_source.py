"""Tie-independent nearest-source diagnostics on frozen root lists; no eigensolve.

All counted positive-height strip roots in this payload are real. For a fixed
source x+iy the nearest real root minimizes |root-x|, so two adjacent sorted
neighbors suffice. The comparison is many-to-one, explicitly not an injective
matching or an optimal bottleneck assignment.
"""
from pathlib import Path
import sys,json,csv,bisect,time,hashlib
sys.dont_write_bytecode=True
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P/'roots'))
import mpmath as mp
from census import references,reference_binding

def main():
    started=time.process_time();mp.mp.dps=200
    refs={w:references(w) for w in ['zeta','dh','plant']};rows=[]
    for f in sorted((P/'roots/results').glob('*.json')):
        d=json.loads(f.read_text());world=d.get('world')
        if world not in refs:continue
        T=mp.mpf(d['cutoffs']['fixed_c1_4']['T'])
        targets=[r for r in refs[world] if 0<r['re']<T and abs(r['im'])<mp.mpf('.5')]
        actual=[r for r in d['roots'] if 0<mp.mpf(r['z_re'])<T and abs(mp.mpf(r['z_im']))<mp.mpf('.5')]
        assert all(mp.mpf(r['z_im'])==0 for r in actual), 'Non-real candidate requires general nearest search'
        row=dict(world=world,m=d['m'],parity=d['parity'],is_global=d['parity']==d['global_parity'],source_count=len(targets),T=mp.nstr(T,30))
        for scope in ['numerator','full_transform']:
            selected=actual if scope=='full_transform' else [r for r in actual if r['kind'].startswith('polynomial')]
            real=sorted(mp.mpf(r['z_re']) for r in selected);assert real
            distances=[]
            for target in targets:
                j=bisect.bisect_left(real,target['re']);indices=[i for i in [j-1,j] if 0<=i<len(real)]
                distances.append(min(abs(mp.mpc(real[i]-target['re'],-target['im'])) for i in indices))
            row[scope+'_candidate_count']=len(real)
            row[scope+'_max_nearest_distance']=mp.nstr(max(distances),40)
            row[scope+'_max_nearest_over_T']=mp.nstr(max(distances)/T,30)
            for label,tol in [('1e_2','1e-2'),('1e_6','1e-6'),('1e_12','1e-12')]:
                row[scope+'_source_close_'+label]=sum(v<mp.mpf(tol) for v in distances)
        rows.append(row)
    assert len(rows)==1107 and sum(r['is_global'] for r in rows)==855
    with (P/'NEAREST_SOURCE.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    receipt=dict(status='COMPLETE_TIE_INDEPENDENT_NEAREST_SOURCE_DIAGNOSTIC',physical_cases=len(rows),global_cases=sum(r['is_global'] for r in rows),precision_dps=200,CPU_seconds=time.process_time()-started,method='MP sorted-real-root neighbor search, one source at a time; many-to-one, not injective; source and candidate positive heights below primary T, abs(Im)<1/2',references={w:reference_binding(w) for w in refs},script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),csv_sha256=hashlib.sha256((P/'NEAREST_SOURCE.csv').read_bytes()).hexdigest(),m300_global=[r for r in rows if r['m']==300 and r['is_global']],scope='Frozen decimal polynomial roots and supplied numerical source census, not an exact-source eigenvector certificate')
    (P/'NEAREST_SOURCE.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt['m300_global'],indent=2));print('CPU seconds',receipt['CPU_seconds'])
if __name__=='__main__':main()
