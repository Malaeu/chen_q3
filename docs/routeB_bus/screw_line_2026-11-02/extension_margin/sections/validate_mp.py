"""80-digit full-old-history validation for the short section n16,mesh32.
All q refinements are aggregated from one32-bin fresh Gram.
DIAGNOSTIC_NEVER_A_PROOF; no directed-rounding certificate.
"""
from pathlib import Path
from functools import lru_cache
import sys,json,csv,time
import mpmath as mp
ROOT=Path(__file__).resolve().parent
CORE=ROOT.parents[1]/'innovation_law'/'core'
sys.path.insert(0,str(CORE))
from scan import source

def main():
    start=time.monotonic();mp.mp.dps=80;mesh=32;n=16;qmax=32
    h=mp.mpf(1)/mesh;a=mp.log(n);delta=mp.log(mp.mpf(n+1)/n);p=int(mp.floor(a/h));end=p*h
    raw=json.loads((CORE/'zeta_mesh32_dps100.json').read_text());rr=list(map(mp.mpf,raw['r_values']))
    gf,_=source('zeta',a+delta);g=lru_cache(None)(gf)
    def cov(l,r,s,t):return g(r-t)-g(r-s)-g(l-t)+g(l-s)
    intervals=[(i*h,(i+1)*h) for i in range(p)]+[(end,a)]
    fresh=[(a+j*delta/qmax,a+(j+1)*delta/qmax) for j in range(qmax)]
    C=mp.matrix(p+1)
    for i in range(p):
        for j in range(p):C[i,j]=rr[abs(i-j)]
        C[i,p]=C[p,i]=cov(*intervals[i],end,a)
    C[p,p]=-2*g(a-end)
    V=mp.matrix([[cov(*old,*new) for new in fresh] for old in intervals])
    F=mp.matrix([[cov(*x,*y) for y in fresh] for x in fresh])
    LC=mp.cholesky(C);A=(LC**-1)*V;G=A.T*A
    partialpivot=LC[p,p]**2
    print('MP80 Gram and old whitening complete',time.monotonic()-start,flush=True)
    floatrows=list(csv.DictReader((ROOT/'representative_q_refinement.csv').open()));out=[]
    for q in (1,4,8,16,32):
        group=mp.matrix(qmax,q);width=qmax//q
        for i in range(qmax):group[i,i//width]=1
        ff=group.T*F*group;gg=group.T*G*group;LF=mp.cholesky(ff);Li=LF**-1
        W=Li*gg*Li.T;mu=1-mp.eigsy(W,eigvals_only=True)[q-1]
        S=ff-gg;direct=mp.eigsy(Li*S*Li.T,eigvals_only=True)[0]
        oldrow=next(x for x in floatrows if x['world']=='zeta' and int(x['mesh'])==mesh and int(x['n'])==n and int(x['q'])==q)
        discrepancy=abs(mu-mp.mpf(oldrow['mu']))
        row=dict(world='zeta',mesh=mesh,n=n,q=q,dps=80,old_uniform_count=p,old_count_with_partial=p+1,delta=mp.nstr(delta,60),mu=mp.nstr(mu,75),float_mu=oldrow['mu'],absolute_float_change=mp.nstr(discrepancy,30),partial_old_pivot=mp.nstr(partialpivot,60),min_fresh_pivot=mp.nstr(min(LF[i,i]**2 for i in range(q)),50),normalized_schur_error=mp.nstr(abs(mu-direct),30),fresh_gram_entrywise_norm_condition_upper=mp.nstr(mp.norm(ff,1)*mp.norm(ff**-1,1),30))
        assert discrepancy<mp.mpf('1e-7')
        assert abs(mu-direct)<mp.mpf('1e-70')
        out.append(row);print(json.dumps(row),flush=True)
    assert all(mp.mpf(y['mu'])<=mp.mpf(x['mu']) for x,y in zip(out,out[1:]))
    assert mp.mpf(out[-1]['mu'])<mp.mpf('.1')
    with (ROOT/'mp_validation.csv').open('w',newline='') as f:
        wr=csv.DictWriter(f,fieldnames=out[0]);wr.writeheader();wr.writerows(out)
    (ROOT/'mp_validation.json').write_text(json.dumps(dict(status='DIAGNOSTIC_NEVER_A_PROOF',claim='finite sampled mu<0.1 at n16 within short-form range; no all-node positivity claim',seconds=time.monotonic()-start,rows=out),indent=2)+'\n')
if __name__=='__main__':main()
