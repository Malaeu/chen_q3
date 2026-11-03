"""Independent finite fresh-form margin checks. DIAGNOSTIC_NEVER_A_PROOF."""
from pathlib import Path
from functools import lru_cache
import sys,csv,json,hashlib
import mpmath as mp
OUT=Path(__file__).resolve().parent
SRC=OUT.parents[1]/'innovation_law'/'core'/'scan.py'
sys.path.insert(0,str(SRC.parent))
from scan import source

def cell(delta_name,q,dps):
    mp.mp.dps=dps
    a=mp.log(16)
    delta=mp.log(mp.mpf(17)/16) if delta_name=='section16' else mp.mpf(delta_name)
    old=[a*(i+1)/4 for i in range(4)]
    fresh=[delta*(j+1)/q for j in range(q)]
    fun,_=source('zeta',a+delta)
    g=lru_cache(None)(fun)
    def K(s,t):return g(s-t)-g(s)-g(t)
    C=mp.matrix([[K(s,t) for t in old] for s in old])
    F=mp.matrix([[K(s,t) for t in fresh] for s in fresh])
    V=mp.matrix([[K(s,a+h)-K(s,a) for h in fresh] for s in old])
    B=mp.matrix([[K(s,a+h) for h in fresh] for s in old])
    D=mp.matrix([[K(a+s,a+t) for t in fresh] for s in fresh])
    minC=mp.eigsy(C,eigvals_only=True)[0];minF=mp.eigsy(F,eigvals_only=True)[0]
    guard=mp.mpf(10)**(-dps+20)
    if min(minC,minF)<=guard:raise ArithmeticError('C/F positivity unresolved')
    Ci=mp.cholesky(C)**-1;Fi=mp.cholesky(F)**-1
    A=Ci*V*Fi.T
    ev=mp.eigsy(A*A.T,eigvals_only=True)
    mu=1-ev[len(ev)-1]
    S=F-V.T*(C**-1)*V
    S_direct=D-B.T*(C**-1)*B
    white=Fi*S*Fi.T
    mu_direct=mp.eigsy(white,eigvals_only=True)[0]
    error=mp.norm(S-S_direct)
    relativewhite=abs(mu-mu_direct)
    assert error<mp.mpf(10)**(-dps+12)
    assert relativewhite<mp.mpf(10)**(-dps+12)
    row=dict(case=delta_name,q=q,dps=dps,a=mp.nstr(a,30),delta=mp.nstr(delta,30),mu=mp.nstr(mu,dps),min_C=mp.nstr(minC,30),min_F=mp.nstr(minF,30),min_S=mp.nstr(mp.eigsy(S,eigvals_only=True)[0],30),point_increment_S_error=mp.nstr(error,20),normalized_S_mu_error=mp.nstr(relativewhite,20))
    print(json.dumps(row),flush=True)
    return row

def main():
    rows=[]
    for name in ('section16','0.001','0.00001'):
        block=[cell(name,q,80 if name=='section16' else 70) for q in (1,4,8,16,32)]
        assert all(mp.mpf(y['mu'])<=mp.mpf(x['mu']) for x,y in zip(block,block[1:]))
        rows.extend(block)
    high=cell('section16',32,100);rows.append(high)
    mp.mp.dps=110
    err=abs(mp.mpf(rows[4]['mu'])-mp.mpf(high['mu']))
    assert err<mp.mpf('1e-58')
    with (OUT/'finite_margin_checks.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
    result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',all_C_F_positive=True,all_nested_q_mu_nonincreasing=True,all_sampled_S_positive=all(mp.mpf(x['min_S'])>0 for x in rows),section16_q32_precision_abs_change=mp.nstr(err,30),source_script_sha256=hashlib.sha256(SRC.read_bytes()).hexdigest(),checks=rows)
    (OUT/'finite_margin_checks.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
