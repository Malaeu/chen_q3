"""Bounded independent review of frozen zeta-only continuation candidate."""
from pathlib import Path
from fractions import Fraction
import sys,json,hashlib,time,importlib.util,resource
sys.path.insert(0,'/workspace/conditioning_deps')
import mpmath as mp
from flint import arb,acb_poly,ctx

P=Path(__file__).resolve().parent;BASE=P.parent;ROOT=BASE/'roots'
resource.setrlimit(resource.RLIMIT_CPU,(45,47))
mp.mp.dps=260
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def module(name,path):
    s=importlib.util.spec_from_file_location(name,path);q=importlib.util.module_from_spec(s);s.loader.exec_module(q);return q
def own_poly(c,m):
    N=acb_poly([arb(c[0])]);D=acb_poly([0,1]);s=arb(2).sqrt()
    for n in range(1,m+1):
        a=arb(n*n)/arb(m*m);factor=acb_poly([-a,1]);N=N*factor+D*(s*arb(c[n]));D*=factor
    return N

def main():
    begin=time.process_time();manifest=json.loads((ROOT/'continuation_frozen_manifest.json').read_text())
    assert all(sha(ROOT/name)==value for name,value in manifest.items())
    helper=module('real_continuation_v1',ROOT/'real_continuation_v1.py');sys.modules['real_continuation_v1']=helper
    rows=[];guardrows=[];sources={}
    for m in [190,206]:
        rp=ROOT/f'results/zeta_even_m{m}.json';ref=json.loads(rp.read_text());sp=Path(ref['source_vector_path']);blob=sp.read_bytes();data=json.loads(blob);c=data['v_even0'];prev=ROOT/f'results/zeta_even_m{m-1}.json'
        assert sha(sp)==ref['source_vector_sha256']
        t=time.process_time();balls,info=helper.isolate_real(c,m,'even',prev,sp,expected_source_sha256=sha(sp));solve=time.process_time()-t
        ctx.prec=max(3000,2*info['bits']);pol=own_poly(c,m);assert pol.degree()==m and not pol[m].contains(0)
        last=None;lastball=None;maxdiff=mp.mpf(0);maxradius=mp.mpf(0)
        old=sorted((mp.mpf(r['u_re']) for r in ref['roots'] if r['kind'].startswith('polynomial')))
        assert len(old)==len(balls)==len(info['brackets'])==m
        for i,(b,br) in enumerate(zip(balls,info['brackets'])):
            lo,hi=Fraction(br['left']),Fraction(br['right']);assert lo<hi and (last is None or last<lo)
            assert all(not lo<=Fraction(n*n,m*m)<=hi for n in range(1,m+1))
            left,right=pol(arb(br['left'])),pol(arb(br['right']))
            assert (left.real>0 and right.real<0) or (left.real<0 and right.real>0)
            assert left.imag.is_zero() and right.imag.is_zero() and b.imag.is_zero()
            assert b.real.contains(arb(br['left'])) and b.real.contains(arb(br['right']))
            assert b.real.rad()<arb('1e-165') and (lastball is None or lastball.real<b.real)
            assert b.real>0  # Verifies physical classification for both tested cells.
            u=mp.mpf(b.real.mid().str(220,radius=False));maxdiff=max(maxdiff,abs(u-old[i]));maxradius=max(maxradius,mp.mpf(b.real.rad().str(25,radius=False)))
            last=hi;lastball=b
        assert maxdiff<mp.mpf('2e-165')
        rows.append(dict(m=m,world='zeta',parity='even',status='PASS',degree=m,continued_cpu_seconds=solve,independent_endpoint_recheck=True,exact_disjoint_pole_free_brackets=m,raw_real_positive_u_roots=m,
                         max_midpoint_difference_from_stored_full_census=mp.nstr(maxdiff,45),max_output_u_radius=mp.nstr(maxradius,35),source_sha256=sha(sp),stored_full_census_sha256=sha(rp),
                         previous_result_sha256=info['previous_result_sha256'],missing_seed_count=info['missing_root_count']))
        sources[m]=(c,prev,sp,data)
        print(json.dumps(rows[-1]),flush=True)
    c,prev,sp,data=sources[190]
    def reject(name,callback):
        try:callback()
        except Exception as exc:guardrows.append(dict(guard=name,status='REJECTED',type=type(exc).__name__,message=str(exc)))
        else:raise AssertionError('Invalid continuation accepted: '+name)
    reject('wrong_parity',lambda:helper.isolate_real(c,190,'odd',prev,sp))
    reject('nonadjacent_previous_dimension',lambda:helper.isolate_real(c,191,'even',prev,sp))
    reject('current_snapshot_sha_mismatch',lambda:helper.isolate_real(c,190,'even',prev,sp,expected_source_sha256='0'*64))
    reject('current_coefficients_mismatch',lambda:helper.isolate_real(['0']+c[1:],190,'even',prev,sp))
    stale=json.loads(prev.read_text());stale['source_vector_sha256']='0'*64;fixture=P/'continuation_stale_previous.json';fixture.write_text(json.dumps(stale))
    reject('stale_previous_source_sha',lambda:helper.isolate_real(c,190,'even',fixture,sp))
    wrongworld=json.loads(prev.read_text());wrongworld['world']='plant';fixture2=P/'continuation_wrongworld_previous.json';fixture2.write_text(json.dumps(wrongworld))
    reject('previous_source_world_mismatch',lambda:helper.isolate_real(c,190,'even',fixture2,sp))
    dhp=BASE/'spectra/vectors/dh_m190.json';dhd=json.loads(dhp.read_text())
    reject('non_zeta_world',lambda:helper.isolate_real(dhd['v_even0'],190,'even',prev,dhp))
    # Exercise the exact candidate integration with writes redirected into review/.
    candidate=module('reviewed_census_continuation_candidate',ROOT/'census_continuation_candidate.py');sandbox=P/'continuation_integration_sandbox';sandbox.mkdir(exist_ok=True);candidate.OUT=sandbox
    real=helper.isolate_real
    def fail(*args,**kwargs):raise RuntimeError('review planted continuation failure')
    helper.isolate_real=fail
    try:
        fallback=candidate.run(BASE/'spectra/vectors/zeta_m16.json',parity='even')
        assert fallback['checks']['continuation_fallback']['type']=='RuntimeError'
        assert fallback['checks']['method']=='Flint complete complex polynomial isolation'
        dh=candidate.run(BASE/'spectra/vectors/dh_m16.json',parity='even')
        assert 'continuation_fallback' not in dh['checks'] and dh['checks']['method']=='Flint complete complex polynomial isolation'
    finally:helper.isolate_real=real
    result=dict(status='PASS_FROZEN_ZETA_ONLY_CONTINUATION_REVIEW',frozen_hashes=manifest,pilots=rows,negative_guards=guardrows,
                broad_exception_falls_back_to_flint=True,non_zeta_caller_skips_fast_path=True,total_cpu_seconds=time.process_time()-begin,
                scope='Frozen decimal-vector finite polynomial software review only. No new eigenproblem, source-zero seed, continuum/RH claim, or 180-digit accuracy claim. Output has 180 rendering digits with the actual enclosure radius retained.')
    (P/'continuation_review.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['frozen_hashes','pilots','negative_guards']}),flush=True)

if __name__=='__main__':main()
