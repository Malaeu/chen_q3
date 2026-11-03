"""Bounded optional LOW-source refinement probe; never changes producer files.

Prediction0.5: a shifted real-Arb solve refines the independently rebuilt LOW
ground more cheaply than another full Householder ordering. Kill above40CPU s,
or if residual/ordering-perturbation/overlap gates fail. No adoption in this probe.
"""
from pathlib import Path
import sys,time,json,signal,resource
sys.path.insert(0,'/workspace/conditioning_deps')
import gmpy2 as g
from flint import arb,arb_mat,fmpq,ctx
import analytic_source as source
P=Path(__file__).resolve().parent
def main():
    def stop(s,f):raise TimeoutError('shifted LOW probe40CPU budget')
    signal.signal(signal.SIGXCPU,stop);resource.setrlimit(resource.RLIMIT_CPU,(40,45));started=time.process_time();wall=time.monotonic()
    s=json.loads((P.parent/'spectra/vectors/zeta_m160.json').read_text());low=s['low_precision_bits'];high=s['precision_bits'];ctx.prec=high+160
    A,meta=source.build(160,low);g.get_context().precision=high+160
    M=arb_mat([[arb(fmpq(*map(int,g.mpfr(x,low).as_integer_ratio()))) for x in row] for row in A['zeta'][0]])
    sig=arb(s['lambda_even0'])-arb(s['even_gap'])/128;B=M-arb_mat(161,161,[sig if i==j else 0 for i in range(161) for j in range(161)])
    v=arb_mat([[arb(x)] for x in s['v_even0']]);history=[]
    for it in range(3):
        t=time.process_time();w=B.solve(v,algorithm='approx');norm=(w.transpose()*w)[0,0].sqrt();v=arb_mat([[(w[i,0]/norm).mid()] for i in range(161)])
        lam=(v.transpose()*M*v)[0,0];res=M*v-v*lam
        r=max(abs(res[i,0]).upper() for i in range(161));old=[arb(x) for x in s['v_even0_low']]
        delta=max(abs(v[i,0]-old[i]).upper() for i in range(161))
        history.append(dict(iteration=it+1,solve_CPU_seconds=time.process_time()-t,rayleigh=str(lam),max_residual=str(r),max_difference_from_native_low=str(delta)))
        print(history[-1],flush=True)
    z=dict(status='PERFORMANCE_PROBE_ONLY_NOT_ADOPTED',m=160,low_bits=low,solve_bits=ctx.prec,source_CPU=meta['seconds'],history=history,CPU_seconds=time.process_time()-started,wall_seconds=time.monotonic()-wall,source_changed=False)
    (P/'shifted_low_probe.json').write_text(json.dumps(z,indent=2)+'\n')
if __name__=='__main__':main()
