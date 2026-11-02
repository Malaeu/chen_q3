"""V expectation gaps in the CCM eigenbasis; DIAGNOSTIC_NEVER_A_PROOF."""
from pathlib import Path
import sys,argparse,json,csv,hashlib,time
import mpmath as mp
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P.parent))
from v_forms import build_forms
def fmt(x):return mp.nstr(x,100)
def run(window_m,Ns,dps,order,tag):
    start=time.monotonic();forms=build_forms(window_m,max(Ns),dps,order);outputs=[]
    for N in Ns:
        K=forms['K'][:N+1,:N+1];A=forms['arch'][:N+1,:N+1];X=forms['spatial'][:N+1,:N+1];B=A+X
        ev,U=mp.eigsy(K);h=forms['h'][:N+1,:];h/=mp.norm(h)
        if mp.fdot(U[:,0],h)<0:U[:,0]=-U[:,0]
        AU=A*U;XU=X*U;aa=[mp.fdot(U[:,i],AU[:,i]) for i in range(N+1)];xx=[mp.fdot(U[:,i],XU[:,i]) for i in range(N+1)]
        vv=[a+x for a,x in zip(aa,xx)]
        j7=min(range(1,8),key=lambda i:vv[i]);jall=min(range(1,N+1),key=lambda i:vv[i])
        ah=mp.fdot(h,A*h);xh=mp.fdot(h,X*h);vh=ah+xh
        row=dict(window_m=window_m,N=N,L=fmt(forms['L']),literal=N==window_m,dps=dps,order=order,
            lambda0=fmt(ev[0]),lambda1=fmt(ev[1]),V0=fmt(vv[0]),V1=fmt(vv[1]),gap_V1_minus_V0=fmt(vv[1]-vv[0]),
            cluster_min_index=j7,cluster_min_gap=fmt(vv[j7]-vv[0]),all_even_min_index=jall,all_even_min_gap=fmt(vv[jall]-vv[0]),
            projected_h_arch=fmt(ah),projected_h_spatial=fmt(xh),projected_h_V=fmt(vh),projected_h_V_minus_V0=fmt(vh-vv[0]),
            w0=fmt(mp.fdot(U[:,0],h)**2),eigenpair_residual=fmt(mp.norm(K*U-U*mp.diag(ev))),
            V_basis_offdiagonal_max=fmt(max(abs(z) for z in (U.T*B*U-mp.diag(vv)))))
        levels=[dict(i=i,lambda_i=fmt(ev[i]),arch=fmt(aa[i]),spatial=fmt(xx[i]),V=fmt(vv[i]),V_minus_V0=fmt(vv[i]-vv[0])) for i in range(N+1)]
        outputs.append(dict(summary=row,levels=levels,first_eight_vectors=[[fmt(U[j,i]) for j in range(N+1)] for i in range(8)],
            projected_h_unit_coefficients=[fmt(x) for x in h],source_v_forms_sha256=hashlib.sha256((P.parent/'v_forms.py').read_bytes()).hexdigest(),
            status='DIAGNOSTIC_NEVER_A_PROOF'))
        (P/f'{tag}_window{window_m}.json').write_text(json.dumps(outputs,indent=2)+'\n')
        print('CELL',window_m,N,'V0',mp.nstr(vv[0],14),'g',mp.nstr(vv[1]-vv[0],14),'hV',mp.nstr(vh,14),'mins',j7,jall,'seconds',time.monotonic()-start,flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--window',type=int,required=True);p.add_argument('--N',nargs='+',type=int,required=True)
    p.add_argument('--dps',type=int,default=160);p.add_argument('--order',type=int,default=128);p.add_argument('--tag',default='main')
    a=p.parse_args();run(a.window,a.N,a.dps,a.order,a.tag)
