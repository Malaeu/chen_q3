"""Stored-HIGH controls of frozen LOW-refinement helper; no HIGH eigensolve."""
from pathlib import Path
import sys,json,hashlib,time,resource,importlib.util
sys.path[:0]=['/workspace/conditioning_deps',str(Path(__file__).resolve().parent.parent/'inputs')]
import gmpy2 as g
from analytic_source import build

P=Path(__file__).resolve().parent;BASE=P.parent;S=BASE/'spectra';F=g.mpfr
resource.setrlimit(resource.RLIMIT_CPU,(60,63))
EXPECTED='0270354e1c1aac059408728f38748387446b318cef87c3f939996af3707e6bdb'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def put(rows,start):
    out=dict(status='PASS_COMPLETED_STORED_HIGH_CONTROLS',helper_sha256=EXPECTED,rows=rows,total_cpu_seconds=time.process_time()-start,
             scope='Independent LOW/HIGH source rebuilds, frozen LOW helper and stored HIGH native pairs; no HIGH eigensolve. Numerical point-matrix diagnostics only, not source/eigenspace interval bounds.')
    (P/'shifted_low_review.json').write_text(json.dumps(out,indent=2)+'\n')
    return out
def mpstr(x):return str(x)

def main():
    start=time.process_time();assert sha(S/'shifted_low_candidate.py')==EXPECTED
    spec=importlib.util.spec_from_file_location('frozen_shifted_low_candidate',S/'shifted_low_candidate.py');helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
    rows=[]
    for m in [160,300]:
        zpath=S/f'vectors/zeta_m{m}.json';zdata=json.loads(zpath.read_text());lb=zdata['low_precision_bits'];hb=zdata['source_precision_bits']
        low,_=build(m,lb);high,_=build(m,hb)
        cases=[('zeta','even'),('zeta','odd')]+([('dh','odd')] if m==300 else [])
        for world,parity in cases:
            vp=S/f'vectors/{world}_m{m}.json';data=json.loads(vp.read_text());block=next(b for b in data['blocks'] if b['parity']==parity);j=0 if parity=='even' else 1
            g.get_context().precision=hb+128;bitslo=block['solver_bits_low'];bitshi=block['solver_bits_high']
            H=dict(bits=bitshi,lambda_=[F(block['lambda0']),F(block['lambda1'])],v=[list(map(F,block['v0'])),list(map(F,block['v1']))],residual_infinity=list(map(F,block['residual_infinity'])))
            H['lambda']=H.pop('lambda_');t=time.process_time();answer=helper.refine(low[world][j],bitslo,high[world][j],bitshi,H);elapsed=time.process_time()-t
            assert answer['lambda_'][1] is None and answer['v'][1] is None and answer['residual_infinity'][1] is None
            vv=answer['v'][0];la=answer['lambda_'][0];AL=[[F(x,bitslo) for x in row] for row in low[world][j]];AH=[[F(x,bitshi) for x in row] for row in high[world][j]]
            normerr=abs(sum((x*x for x in vv),F(0))-1)
            res=max(abs(sum((a*x for a,x in zip(row,vv)),F(0))-la*y) for row,y in zip(AL,vv))
            native=list(map(F,data['v_'+parity+'0_low']));vd=min(max(abs(x-y) for x,y in zip(vv,native)),max(abs(x+y) for x,y in zip(vv,native)))
            entry=max(abs(a-b) for ar,br in zip(AL,AH) for a,b in zip(ar,br));op=len(AL)*entry
            assert answer['point_entry_difference']==entry and answer['point_operator_difference']==op
            assert normerr<F('1e-25') and vd<F('1e-25') and res<2*answer['residual_infinity'][0]
            assert answer['correspondence_gate'] and answer['shift_below_low_ground_margin']>0
            assert answer['weyl_radius']<(H['lambda'][1]-H['lambda'][0])/1024
            assert abs(la-H['lambda'][0])<(H['lambda'][1]-H['lambda'][0])/8
            corrections=[]
            if world=='zeta':
                roots=json.loads((BASE/f'roots/results/zeta_{parity}_m{m}.json').read_text());T=F(roots['cutoffs']['fixed_c1_4']['T']);L=F(data['L_low']);Om=2*g.const_pi()*m/L
                rr=[r for r in roots['roots'] if r['kind']=='polynomial_real' and 0<F(r['z_re'])<T]
                for k in sorted({0,len(rr)//2,len(rr)-1}):
                    z=F(rr[k]['z_re']);u=(z/Om)**2;aa=[F(n*n)/F(m*m) for n in range(1,m+1)]
                    if parity=='even':
                        weights=[g.sqrt(F(2))*v for v in vv[1:]];value=vv[0]+sum((w*u/(u-a) for w,a in zip(weights,aa)),F(0));der=sum((-w*a/(u-a)**2 for w,a in zip(weights,aa)),F(0))
                    else:
                        weights=[F(n)*vv[n-1] for n in range(1,m+1)];value=sum((w/(u-a) for w,a in zip(weights,aa)),F(0));der=sum((-w/(u-a)**2 for w,a in zip(weights,aa)),F(0))
                    correction=abs(value/der*Om/(2*g.sqrt(u)));assert correction<F('1e-25')
                    corrections.append(dict(root_id=rr[k]['root_id'],physical_newton_correction=str(correction)))
            row=dict(m=m,world=world,parity=parity,status='PASS',low_actual_solver_bits=bitslo,high_actual_solver_bits=bitshi,low_refinement_arithmetic_bits=answer['arithmetic_bits'],helper_cpu_seconds=elapsed,
                     independent_actual_point_residual=str(res),helper_reported_residual=str(answer['residual_infinity'][0]),normalization_error=str(normerr),vector_difference_from_native_LOW=str(vd),point_operator_difference=str(op),weyl_radius=str(answer['weyl_radius']),shift_margin=str(answer['shift_below_low_ground_margin']),
                     LOW_lambda1_vector1_residual1_all_null=True,selected_physical_root_corrections=corrections,stored_vector_sha256=sha(vp))
            rows.append(row);put(rows,start);print(json.dumps({k:v for k,v in row.items() if k not in ['selected_physical_root_corrections','stored_vector_sha256']}),flush=True)
    result=put(rows,start);assert len(rows)==5;print(json.dumps({k:v for k,v in result.items() if k!='rows'}),flush=True)

if __name__=='__main__':main()
