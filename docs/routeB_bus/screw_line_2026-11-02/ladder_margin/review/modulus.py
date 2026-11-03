"""Explicit source modulus and finite-cardinality perturbation budget.
All decimal evaluations here are diagnostic, not directed-rounding bounds.
"""
from pathlib import Path
import sys,csv,json
import mpmath as mp
OUT=Path(__file__).resolve().parent
CORE=OUT.parents[1]/'innovation_law'/'core'
sys.path.insert(0,str(CORE));from scan import source

def main():
    mp.mp.dps=80;rows=[];checks=[]
    for W in (3,5,7):
        T=mp.log(W);g,atoms=source('zeta',T)
        cstar=mp.euler+mp.log(8*mp.pi)+mp.pi/2
        lipschitz=cstar/2+4*mp.sinh(T/2)+mp.fsum(c for a,c,n in atoms if n<=W)
        def omega(e):
            z=mp.exp(-e/2)
            arch=e*(mp.exp(3*e/2)/2+mp.atanh(z)+mp.atan(z))
            return arch+e*lipschitz
        for M in (32,64):
            e=mp.mpf(1)/(2*M)
            # Upper count; exact duplicate removal in the certificate can only
            # reduce the number of rows. Omit origin; one endpoint per r included.
            count=sum(int(mp.floor(M*mp.log(mp.mpf(W)/r)))+1 for r in range(1,W+1))-1
            entry=omega(2*e)+2*omega(e)
            rows.append(dict(window=W,T=mp.nstr(T,30),mesh=M,epsilon=mp.nstr(e,30),omega_epsilon=mp.nstr(omega(e),40),kernel_entry_error=mp.nstr(entry,40),node_count_upper=count,spectral_norm_budget_at_count_upper=mp.nstr(count*entry,40)))
            pairs=[(mp.mpf(0),e),(T-e,T),(T/3,T/3+e),(T/2,T/2+e)]
            pairs +=[(max(0,a-e/2),min(T,a+e/2)) for a,c,n in atoms if n<=W]
            for s,t in pairs:
                d=abs(t-s);observed=abs(g(t)-g(s));bound=omega(d)
                assert observed<=bound
                checks.append(dict(window=W,mesh=M,s=mp.nstr(s,40),t=mp.nstr(t,40),source_difference=mp.nstr(observed,40),modulus=mp.nstr(bound,40),ratio=mp.nstr(observed/bound,30)))
    for name,data in [('modulus_budget.csv',rows),('modulus_checks.csv',checks)]:
        with (OUT/name).open('w',newline='') as f:
            w=csv.DictWriter(f,fieldnames=data[0]);w.writeheader();w.writerows(data)
    result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',dps=80,all_checks_pass=True,max_observed_to_bound_ratio=max(float(x['ratio']) for x in checks),table=rows)
    (OUT/'modulus_summary.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
if __name__=='__main__':main()
