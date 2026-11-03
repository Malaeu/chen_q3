"""Independent high-precision quadrature regression at the smallest pilot ground.

The pinned reference is copied in memory; only precision/iteration tolerance and
moment export change. No eigenproblem, source-zero input or RH premise.
"""
from pathlib import Path
import sys,types,time,json,hashlib,signal,resource
sys.path.insert(0,'/workspace/conditioning_deps')
import gmpy2 as g
import numpy as np
import analytic_source as analytic
P=Path(__file__).resolve().parent
def main():
    start=time.monotonic();cpu=time.process_time();bits=2400;m=300
    def stop(signum,frame):raise TimeoutError('Ground-scale source validation CPU budget180seconds')
    signal.signal(signal.SIGXCPU,stop);resource.setrlimit(resource.RLIMIT_CPU,(180,190))
    original=(P/'source_50777d4.py').read_text();text=original.replace('precision=400','precision=2400').replace("f('1e-115')","f('1e-700')")
    assert text!=original
    text=text.replace('out={};z=g.exp(-L/2)','out={};betas={};z=g.exp(-L/2)').replace('out[world]=A','out[world]=A;betas[world]=beta').replace('return out\n','return out,betas\n')
    module=types.ModuleType('independent_high_quad');module.__file__=str(P/'source_50777d4.py');exec(compile(text,module.__file__,'exec'),module.__dict__)
    print('START reference2400bit8panelGL768',flush=True);g.get_context().precision=bits
    R,beta=module.build(m,768);print('REFERENCE complete CPU',time.process_time()-cpu,flush=True)
    f=g.mpfr;pi=module.pi;L=g.log(m);one=f(1);out={};ds=[one]+[g.sqrt(2)]*m
    for world in ['zeta','dh']:
        E=R[world];O=np.empty((m,m),object);b=beta[world]
        pe=[4*g.sqrt(2)*ds[n]*L**f('1.5')*g.sinh(L/4)/(L*L+16*pi*pi*n*n) for n in range(m+1)]
        po=[32*pi*n*g.sqrt(L)*g.sinh(L/4)/(L*L+16*pi*pi*n*n) for n in range(1,m+1)]
        for i in range(1,m+1):
            O[i-1,i-1]=E[i,i]-2*b[i]/(pi*i)-(pe[i]*pe[i]+po[i-1]*po[i-1] if world=='zeta' else 0)
            for j in range(i+1,m+1):
                v=2/pi*(j*b[i]-i*b[j])/(i*i-j*j)
                if world=='zeta':v-=po[i-1]*po[j-1]
                O[i-1,j-1]=O[j-1,i-1]=v
        out[world]=(E,O)
    w=g.mpc(2*pi/g.log(2),f('.25'));ov=[g.sqrt(2/L)*2*(2*pi*n/L)*g.sin(w*L/2)/(w*w-(2*pi*n/L)**2) for n in range(1,m+1)]
    out['plant']=(R['plant'],out['zeta'][1]+np.array([[4*(a*b).real for b in ov] for a in ov],object))
    rows=[]
    for sourcebits in [2184,2400]:
        A,meta=analytic.build(m,sourcebits)
        g.get_context().precision=bits+80
        for world in ['zeta','dh','plant']:
            for k,parity in enumerate(['even','odd']):
                err=max(abs(x-y) for x,y in zip(A[world][k].flat,out[world][k].flat))
                assert err<g.mpfr('1e-650'),(sourcebits,world,parity,err)
                native_err=max(abs(g.mpfr(x,sourcebits)-y) for x,y in zip(A[world][k].flat,out[world][k].flat))
                assert native_err<g.mpfr('1e-650'),(sourcebits,world,parity,native_err)
                rows.append(dict(source_bits=sourcebits,world=world,parity=parity,max_entry_difference=str(err),native_point_rounded_max_entry_difference=str(native_err)))
    result=dict(status='GROUND_SCALE_SOURCE_NUMERIC_REGRESSION_PASS',m=m,reference_bits=bits,reference_Gauss_order=768,reference_panels=8,gauss_Newton_stop='1e-700',reference_source_sha256=hashlib.sha256(original.encode()).hexdigest(),in_memory_reference_transform_sha256=hashlib.sha256(text.encode()).hexdigest(),analytic_source_sha256=hashlib.sha256((P/'analytic_source.py').read_bytes()).hexdigest(),odd_reference='Assembled from independently quadrature-evaluated beta/diagonal moments with the separately validated parity formulas.',rows=rows,CPU_seconds=time.process_time()-cpu,wall_seconds=time.monotonic()-start,interval_bound=False,eigenvalue_replayed=False)
    (P/'validation_ground_scale_m300.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
if __name__=='__main__':main()
