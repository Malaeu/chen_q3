"""Read-only independent scalar/integration audit of current diagnostic payload."""
from pathlib import Path
import json, hashlib, collections, argparse
import mpmath as mp

P=Path(__file__).resolve().parent;BASE=P.parent

def read(p):return json.loads(p.read_text())
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def close(a,b,tol=mp.mpf('1e-40')):return abs(mp.mpf(a)-mp.mpf(b))<=tol*max(1,abs(mp.mpf(a)),abs(mp.mpf(b)))
def vector_path(raw):
    original=Path(raw)
    return original if original.is_file() else BASE/'spectra/vectors'/original.name

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--complete',action='store_true');args=ap.parse_args()
    issues=[];vs=sorted((BASE/'spectra/vectors').glob('*_m*.json'));rs=sorted((BASE/'roots/results').glob('*_m*.json'))
    source_snapshots={};source_rebindings=[]
    normalization_file=BASE/'SOURCE_BYTE_NORMALIZATION.json'
    normalization=read(normalization_file).get('aliases',[]) if normalization_file.exists() else []
    def source_snapshot(name,value):
        key=(name,value)
        if key in source_snapshots:return source_snapshots[key]
        candidates=[BASE/'inputs'/name,BASE/'spectra'/name,BASE/'roots'/name]
        candidates+=list((BASE/'spectra/producers').glob('*'+value+'*')) if (BASE/'spectra/producers').exists() else []
        candidates+=list((BASE/'roots/producers').glob('*'+value+'*')) if (BASE/'roots/producers').exists() else []
        for source in candidates:
            if source.exists() and digest(source)==value:
                source_snapshots[key]=(str(source.relative_to(BASE)),'exact_bytes');return source_snapshots[key]
        # Accept only the parent's two explicit, byte-verified normalization aliases.
        for alias in normalization:
            current=BASE/alias['current_path'];historical=BASE/alias['historical_path']
            if current.name==name and alias['historical_sha256']==value and current.exists() and historical.exists():
                if digest(current)==alias['current_sha256'] and digest(historical)==value and historical.read_bytes()==current.read_bytes()+b'\n':
                    source_snapshots[key]=(alias['historical_path'],'explicit_one_terminal_LF_alias');return source_snapshots[key]
        source_snapshots[key]=None;return None
    vectors={};ortho_max=mp.mpf(0);norm_max=mp.mpf(0)
    def check(cond,kind,p,detail=''):
        if not cond:issues.append(dict(kind=kind,file=str(p.relative_to(BASE)),detail=detail))
    for p in vs:
        d=read(p);m=d['m'];w=d['world'];vectors[w,m]=d
        mp.mp.dps=max(100,int(d['precision_dps'])+20)
        for name,value in d.get('hashes',{}).items():
            receipt=source_snapshot(name,value)
            check(receipt is not None,'source_hash_mismatch',p,name)
            if receipt and receipt[1]!='exact_bytes':source_rebindings.append(dict(file=str(p.relative_to(BASE)),name=name,stored_sha256=value,reason=receipt[1]))
        check(d['N']==m and 16<=m<=300,'vector_dimensions',p)
        check(len(d['v_even0'])==m+1 and len(d['v_odd0'])==m,'vector_lengths',p)
        for b in d['blocks']:
            v0=list(map(mp.mpf,b['v0']));v1=list(map(mp.mpf,b['v1']))
            ne=max(abs(mp.fsum(x*x for x in v)-1) for v in [v0,v1]);orth=abs(mp.fsum(a*b for a,b in zip(v0,v1)))
            norm_max=max(norm_max,ne);ortho_max=max(ortho_max,orth)
            check(ne<mp.mpf('1e-25'),'normalization',p)
            check(orth<mp.mpf('1e-25') or not b['resolved'],'orthogonality_vs_status',p)
            check(close(b['gap'],mp.mpf(b['lambda1'])-mp.mpf(b['lambda0'])),'block_gap_identity',p)
            check('low_two_orthogonality' in b,'orthogonality_field_missing',p)
            if 'low_two_orthogonality' in b:check(close(orth,b['low_two_orthogonality']),'orthogonality_recount',p)
            if 'lambda1_sign_resolved' in b:
                expected_sign_flag=abs(mp.mpf(b['lambda1']))>1000*mp.mpf(b['eigenvalue_empirical_error'][1])
                check(b['lambda1_sign_resolved']==expected_sign_flag,'signed_second_level_flag',p,b['parity'])
            low_method=b.get('low_method_metadata',{})
            if low_method.get('method')=='LOW_POINT_SHIFTED_REAL_ARB_REFINEMENT_FROM_ORDERED_HIGH':
                check(b.get('lambda1_low') is None,'fabricated_LOW_lambda1',p,b['parity'])
                for field in ['low_residual_infinity','lambda_replay_difference','vector_replay_infinity']:
                    check(len(b.get(field,[]))==2 and b[field][1] is None,'fabricated_LOW_second_pair',p,b['parity']+'/'+field)
                check('NOT_COMPUTED' in low_method.get('lambda1_status',''),'LOW_second_pair_scope',p,b['parity'])
        check(close(d['parity_gap'],mp.mpf(d['lambda_odd0'])-mp.mpf(d['lambda_even0'])),'parity_gap_identity',p)
        lowest=sorted((mp.mpf(d['lambda_'+par+str(k)]),par,k) for par in ['even','odd'] for k in [0,1])
        check(d['global_ground_parity']==lowest[0][1],'global_parity',p)
        check(close(d['global_gap'],lowest[1][0]-lowest[0][0]),'global_gap_identity',p)
        check(d['global_simple_even']==(d['ground_resolved'] and lowest[0][1]=='even'),'simple_even_flag',p)
        check(close(d['L'],mp.log(m)),'physical_length',p)
    root_cells=[];root_residual_samples=[];mp.mp.dps=100
    for p in rs:
        d=read(p)
        if not (16<=d.get('m',0)<=300) or d.get('world') not in ['zeta','dh','plant']:continue
        m=d['m'];w=d['world'];par=d['parity'];root_cells.append((w,m,par))
        reference=d.get('source_reference',{})
        if reference.get('path') and reference.get('sha256'):
            check(source_snapshot(Path(reference['path']).name,reference['sha256']) is not None,'source_reference_hash_mismatch',p)
        if d.get('checks',{}).get('producer_sha256'):
            check(source_snapshot('real_continuation_v1.py',d['checks']['producer_sha256']) is not None,'continuation_helper_hash_mismatch',p)
        if d.get('census_producer_sha256'):
            check(source_snapshot('census.py',d['census_producer_sha256']) is not None,'census_producer_hash_mismatch',p)
        vp=vector_path(d['source_vector_path']);check(vp.is_file(),'missing_vector_file',p)
        if vp.exists():check(d['source_vector_sha256']==digest(vp),'stale_vector_hash',p)
        check(len([r for r in d['roots'] if r['kind'].startswith('polynomial')])==d['checks']['degree'],'polynomial_degree_accounting',p)
        check(d['checks']['isolated_count']==d['checks']['degree'],'isolation_count',p)
        T=mp.mpf(d['cutoffs']['fixed_c1_4']['T']);Om=2*mp.pi*m/mp.log(m)
        expected=(1+(1+mp.log(mp.log(m)))/(4*mp.log(m)))*Om
        check(close(T,expected),'fixed_cutoff',p)
        for key,sm in d['cutoffs'].items():
            cutoff=mp.mpf(sm['T'])
            selected=[r for r in d['roots'] if 0<mp.mpf(r['z_re'])<cutoff and abs(mp.mpf(r['z_im']))<mp.mpf('.5')]
            check(len(selected)==sm['fourier_strip_count'],'strip_recount',p,key)
            check(sum(r['kind']=='forced_external' for r in selected)==sm['structural_external_count'],'exterior_recount',p,key)
            for scope,summary in [('all_fourier',sm),('polynomial_only',sm.get('polynomial_only',{}))]:
                matches=[r for r in d['matches'] if r['cutoff']==key and r.get('matching_scope')==scope]
                check(len(matches)==summary.get('matched_count'),'assignment_count',p,key+'/'+scope)
                check(len({r['root_id'] for r in matches})==len(matches),'reused_root',p,key+'/'+scope)
                check(len({str(r['source_index']) for r in matches})==len(matches),'reused_source',p,key+'/'+scope)
                for label,tol in [('1e_2','1e-2'),('1e_6','1e-6'),('1e_12','1e-12')]:
                    n=sum(mp.mpf(r['abs_deviation'])<mp.mpf(tol) for r in matches)
                    check(summary.get('matched_under_'+label)==n,'threshold_recount',p,key+'/'+scope+'/'+label)
                    check(summary.get('source_unrecovered_at_'+label)==summary.get('source_count',0)-n,'source_unrecovered_recount',p,key+'/'+scope+'/'+label)
                    check(summary.get('fourier_unmatched_at_'+label)==summary.get('fourier_strip_count',0)-n,'fourier_unmatched_recount',p,key+'/'+scope+'/'+label)
                for r in matches:
                    delta=mp.mpc(r['root_re'],r['root_im'])-mp.mpc(r['source_re'],r['source_im'])
                    check(close(abs(delta),r['abs_deviation'],mp.mpf('1e-35')),'match_distance_replay',p)
    coverage={w:sorted(m for ww,m in vectors if ww==w) for w in ['zeta','dh','plant']}
    if args.complete:
        for w,ms in coverage.items():check(ms==list(range(16,301)),'spectral_grid_incomplete',P,f'{w}: {len(ms)}/285')
        for w in ['zeta','dh','plant']:
            even=sorted(m for ww,m,pp in root_cells if ww==w and pp=='even')
            check(even==list(range(16,301)),'even_root_grid_incomplete',P,f'{w}: {len(even)}/285')
        root_keys=set(root_cells)
        for (w,m),d in vectors.items():
            check((w,m,d['global_ground_parity']) in root_keys,'actual_global_root_missing',P,f'{w} m{m} {d["global_ground_parity"]}')
    result=dict(status='PASS_CURRENT_PAYLOAD_SCALAR_AUDIT' if not issues else 'ISSUES_FOUND',complete_grid_required=args.complete,
                spectral_cells=len(vectors),root_cells=len(root_cells),coverage={w:dict(count=len(ms),minimum=min(ms) if ms else None,maximum=max(ms) if ms else None) for w,ms in coverage.items()},
                max_normalization_error=str(norm_max),max_lowpair_orthogonality=str(ortho_max),issues=issues,
                source_snapshot_resolution=[dict(name=k[0],stored_sha256=k[1],resolved=v) for k,v in source_snapshots.items()],source_receipt_rebindings=source_rebindings,
                scope='Read-only scalar, schema, hash, root accounting, assignment and threshold audit; no new CCM eigensolve and no source error enclosure.')
    (P/'payload_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
