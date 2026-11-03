"""Complete literal-source ground diagnostics; empirical precision replay, not proof."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import sys,time,json,argparse,subprocess,hashlib,math,traceback
from pathlib import Path
sys.path[:0]=['/workspace/conditioning_deps',str(Path(__file__).resolve().parent.parent/'inputs')]
import gmpy2 as g
import numpy as np
from scipy.linalg import eigvalsh
from analytic_source import build
P=Path(__file__).resolve().parent;V=P/'vectors';V.mkdir(exist_ok=True)
F=g.mpfr

def atomic(path,obj):
    tmp=path.with_suffix(path.suffix+'.tmp');tmp.write_text(json.dumps(obj,indent=2)+'\n');tmp.replace(path)
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def normalized(v):
    v=list(map(F,v));norm=g.sqrt(sum((x*x for x in v),F(0)));v=[x/norm for x in v]
    if v[max(range(len(v)),key=lambda i:abs(v[i]))]<0:v=[-x for x in v]
    return v

def hexadecimal(x):
    d,e,_=x.digits(16);return ('-' if d[0]=='-' else '')+'0x0.'+d.lstrip('-')+'@'+str(e)

def solve(A,bits):
    n=len(A);data=f'{n} {bits}\n'+'\n'.join(hexadecimal(x) for x in A.flat)+'\n';start=time.monotonic()
    proc=subprocess.run([str(P/'loweig')],input=data,text=True,capture_output=True,check=True)
    a=json.loads(proc.stdout);a['bits']=bits;a['wall_seconds']=time.monotonic()-start;a['lambda']=list(map(F,a['lambda']));a['v']=[normalized(v) for v in a['v']]
    a['residual_infinity']=[max(abs(sum((x*y for x,y in zip(row,v)),F(0))-la*z) for row,z in zip(A,v)) for la,v in zip(a['lambda'],a['v'])]
    return a

def run(m,dps=None,step=40):
    preserve={w for w in ['zeta','dh','plant'] if (V/f'{w}_m{m}.json').exists() and json.loads((V/f'{w}_m{m}.json').read_text()).get('v_even0_low') is not None}
    start=time.monotonic();b0=math.ceil(dps*math.log2(10)) if dps else 6*m+256;b1=b0+128;dps=math.floor(b0*math.log10(2));dpshigh=math.floor(b1*math.log10(2))
    low,ml=build(m,b0);Llow=str(g.log(m));ls={}
    caps={}
    for w in ['zeta','dh','plant']:
        caps[w]=[]
        for A in low[w]:
            ee=eigvalsh(np.array(A,float),subset_by_index=[0,1]);caps[w].append(bool(ee[0]<-1e-6 and ee[1]-ee[0]>1e-6))
        ls[w]=[solve(A,min(b0,512) if cap else b0) for A,cap in zip(low[w],caps[w])]
    high,mh=build(m,b1);hs={}
    for w in ['zeta','dh','plant']:hs[w]=[solve(A,min(b1,640) if cap else b1) for A,cap in zip(high[w],caps[w])]
    hashes={p.name:digest(p) for p in [P.parent/'inputs'/'source_50777d4.py',P.parent/'inputs'/'analytic_source.py',P/'loweig.c']}
    for w in ['zeta','dh','plant']:
        pair=[]
        for p,(lo,hi,A,B) in enumerate(zip(ls[w],hs[w],low[w],high[w])):
            n=len(A);entry=max(abs(x-y) for x,y in zip(A.flat,B.flat));op=n*entry
            diffs=[abs(x-y) for x,y in zip(lo['lambda'],hi['lambda'])]
            vd=[min(max(abs(x-y) for x,y in zip(a,b)),max(abs(x+y) for x,y in zip(a,b))) for a,b in zip(lo['v'],hi['v'])]
            res=[g.sqrt(n)*r for r in hi['residual_infinity']]
            # Deliberately empirical: replay change is included rather than a claimed interval input enclosure.
            errs=[max(op+rr,dd,F(2)**(-lo['bits']+24)*max(F(1),max(abs(x) for x in B.flat))) for rr,dd in zip(res,diffs)]
            gap=hi['lambda'][1]-hi['lambda'][0]
            orth=abs(sum((x*y for x,y in zip(hi['v'][0],hi['v'][1])),F(0)))
            scale=max(F(1),max(abs(x) for x in B.flat))
            high_round=F(2)**(-hi['bits']+24)*scale
            vecerr=2*(res[0]+high_round)/gap if gap>0 else F('inf')
            resolved=gap>1000*max(errs) and vd[0]<F('1e-25') and orth<F('1e-25')
            pair.append(dict(lambda0_sign_resolved=bool(abs(hi['lambda'][0])>1000*errs[0]),lambda1_sign_resolved=bool(abs(hi['lambda'][1])>1000*errs[1]),second_vector_interpretation='diagnostic only; no uniqueness assertion for second eigenvector',solver_bits_low=lo['bits'],solver_bits_high=hi['bits'],parity=['even','odd'][p],lambda0=str(hi['lambda'][0]),lambda1=str(hi['lambda'][1]),gap=str(gap),vector0_high_error_heuristic_l2=str(vecerr),vector0_replay_l2_upper=str(g.sqrt(n)*vd[0]),low_two_orthogonality=str(orth),v0=[str(x) for x in hi['v'][0]],v1=[str(x) for x in hi['v'][1]],residual_infinity=[str(x) for x in hi['residual_infinity']],lambda_replay_difference=[str(x) for x in diffs],vector_replay_infinity=[str(x) for x in vd],source_entry_replay_difference=str(entry),source_operator_replay_estimate=str(op),eigenvalue_empirical_error=[str(x) for x in errs],resolved=bool(resolved),low_solver_seconds=lo['seconds'],high_solver_seconds=hi['seconds'],low_tridiagonal_seconds=lo.get('tridiagonal_seconds'),high_tridiagonal_seconds=hi.get('tridiagonal_seconds'),low_eigen_seconds=lo.get('low_two_eigen_seconds'),high_eigen_seconds=hi.get('low_two_eigen_seconds'),bisection_width=hi['bisection_width']))
        e,o=pair;even0,even1=map(F,[e['lambda0'],e['lambda1']]);odd0,odd1=map(F,[o['lambda0'],o['lambda1']]);pg=odd0-even0
        merged=sorted([(even0,'even',0),(even1,'even',1),(odd0,'odd',0),(odd1,'odd',1)],key=lambda x:x[0]);globalgap=merged[1][0]-merged[0][0];err=max(map(F,e['eigenvalue_empirical_error']+o['eigenvalue_empirical_error']))
        global_resolved=e['resolved'] and o['resolved'] and globalgap>1000*err
        L=g.log(m);T=(1+F('.25')*(1+g.log(L))/L)*2*g.const_pi()*m/L
        fouriererr=g.sqrt(L)*F(e['vector0_high_error_heuristic_l2']);Hscale=g.exp(-g.const_pi()*T/4)
        row=dict(L_low=Llow,v_even0_low=[str(x) for x in ls[w][0]['v'][0]],v_odd0_low=[str(x) for x in ls[w][1]['v'][0]],low_precision_dps=min(x['bits'] for x in ls[w])*math.log10(2)//1,T=str(T),even_FT_real_axis_absolute_error_heuristic=str(fouriererr),nominal_H_exponential_scale_at_T=str(Hscale),FT_precision_margin_ratio=str(fouriererr/Hscale),FT_precision_ok=bool(fouriererr<Hscale*F('1e-20')),schema='literal-ground-v1',status='RESOLVED_NUMERICAL_GROUND' if global_resolved else 'UNRESOLVED_NUMERICAL_GROUND',m=m,N=m,world=w,L=str(g.log(m)),precision_dps=min(x['solver_bits_high'] for x in pair)*math.log10(2)//1,precision_bits=min(x['solver_bits_high'] for x in pair),source_precision_dps=dpshigh,source_precision_bits=b1,low_precision_bits=b0,c=e['v0'],v_even0=e['v0'],v_odd0=o['v0'],lambda_even0=e['lambda0'],lambda_even1=e['lambda1'],lambda_odd0=o['lambda0'],lambda_odd1=o['lambda1'],even_gap=e['gap'],odd_gap=o['gap'],parity_gap=str(pg),global_gap=str(globalgap),global_ground_parity=merged[0][1],ground_resolved=bool(global_resolved),even_ground_resolved=e['resolved'],odd_ground_resolved=o['resolved'],global_simple_even=bool(global_resolved and merged[0][1]=='even'),blocks=pair,source_low=ml,source_high=mh,hashes=hashes,source_id='50777d4-literal-analytic-arch-v1',source_precision_uniform_across_worlds=True,solver='MPFR symmetric Householder, Sturm-bisection lowest two, tridiagonal inverse iteration and reflector backtransform',certificate=False,convergence_interpretation='paired source/eigenpair replay and residual diagnostics; not a rigorous source interval bound',total_cell_seconds=time.monotonic()-start)
        if w not in preserve:atomic(V/f'{w}_m{m}.json',row)
    print(json.dumps(dict(m=m,seconds=time.monotonic()-start,dps_low=dps,dps_high=dpshigh,worlds=[dict(world=w,status=json.loads((V/f'{w}_m{m}.json').read_text())['status']) for w in ['zeta','dh','plant']])),flush=True)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--ms',type=int,nargs='+');ap.add_argument('--start',type=int,default=16);ap.add_argument('--stop',type=int,default=300);ap.add_argument('--dps',type=int);ap.add_argument('--step',type=int,default=40);ap.add_argument('--skip',action='store_true');a=ap.parse_args()
    for m in a.ms or range(a.start,a.stop+1):
        if a.skip and all((V/f'{w}_m{m}.json').exists() and 'v_even0_low' in json.loads((V/f'{w}_m{m}.json').read_text()) and 'FT_precision_ok' in json.loads((V/f'{w}_m{m}.json').read_text()) for w in ['zeta','dh','plant']):continue
        try:run(m,a.dps,a.step)
        except Exception as ex:
            atomic(P/f'failure_m{m}.json',dict(m=m,status='FAILED_NO_GROUND_CLAIM',error=str(ex),traceback=traceback.format_exc()));print('FAILED',m,repr(ex),flush=True)
if __name__=='__main__':main()
