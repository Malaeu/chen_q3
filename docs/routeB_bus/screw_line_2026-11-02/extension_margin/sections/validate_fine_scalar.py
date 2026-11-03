"""MP80 finite scalar section30 on mesh256, Toeplitz innovation whitening.
DIAGNOSTIC_NEVER_A_PROOF. No matrix PSD clipping or discarded old modes.
"""
from pathlib import Path
from functools import lru_cache
import sys,json,csv,time
import mpmath as mp
ROOT=Path(__file__).resolve().parent;CORE=ROOT.parents[1]/'innovation_law'/'core'
sys.path.insert(0,str(CORE));from scan import source

def main():
    start=time.monotonic();mp.mp.dps=80;mesh=256;n=30;h=mp.mpf(1)/mesh
    a=mp.log(n);b=mp.log(n+1);delta=b-a;p=int(mp.floor(a/h));tail=a-p*h
    saved=json.loads((CORE/'zeta_mesh256_dps100.json').read_text());r=list(map(mp.mpf,saved['r_values']));gs=list(map(mp.mpf,saved['g_values']))
    gf,_=source('zeta',b);g=lru_cache(None)(gf)
    ga=[g(a-i*h) for i in range(p+1)];gb=[g(b-i*h) for i in range(p+1)]
    B=[[ga[i+1]-gs[p-i-1]-ga[i]+gs[p-i],gb[i+1]-ga[i+1]-gb[i]+ga[i]] for i in range(p)]
    aa=[];v=r[0];G=mp.matrix(2);check=None;minv=v
    for k in range(p):
        if k:
            reflection=(r[k]-mp.fsum(aa[j-1]*r[k-j] for j in range(1,k)))/v
            aa=[aa[j-1]-reflection*aa[k-j-1] for j in range(1,k)]+[reflection]
            v*=1-reflection**2
        if v<=mp.mpf('1e-60'):raise ArithmeticError('old positive pivot unresolved')
        minv=min(minv,v)
        yy=[B[k][i]-mp.fsum(aa[j-1]*B[k-j][i] for j in range(1,k+1)) for i in range(2)]
        for i in range(2):
            for j in range(2):G[i,j]+=yy[i]*yy[j]/v
        if k==31:
            C=mp.matrix([[r[abs(i-j)] for j in range(32)] for i in range(32)])
            BB=mp.matrix(B[:32]);sol=mp.matrix(32,2)
            for col in range(2):sol[:,col]=mp.lu_solve(C,BB[:,col])
            check=mp.norm(G-BB.T*sol)
            assert check<mp.mpf('1e-70')
    D00=-2*g(tail);D11=-2*g(delta);D01=g(delta)-g(tail+delta)+g(tail)
    pivot=D00-G[0,0]
    assert pivot>0
    mu=1-(G[1,1]+(D01-G[0,1])**2/pivot)/D11
    rows=list(csv.DictReader((ROOT/'all_sections_q1.csv').open()))
    old=next(x for x in rows if x['world']=='zeta' and int(x['mesh'])==mesh and int(x['n'])==n)
    difference=abs(mu-mp.mpf(old['mu']))
    assert difference<mp.mpf('1e-7') and mu<mp.mpf('.1')
    result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',world='zeta',mesh=mesh,n=n,q=1,dps=80,old_uniform_count=p,old_count_with_partial=p+1,mu=mp.nstr(mu,75),float_mu=old['mu'],absolute_float_change=mp.nstr(difference,30),partial_old_pivot=mp.nstr(pivot,60),minimum_old_uniform_innovation=mp.nstr(minv,40),whitening_dense32_check=mp.nstr(check,30),seconds=time.monotonic()-start)
    (ROOT/'fine_scalar_validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
if __name__=='__main__':main()
