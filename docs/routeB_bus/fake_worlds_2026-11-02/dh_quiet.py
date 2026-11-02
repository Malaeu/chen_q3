"""DH quiet kernels and raw capacity; DIAGNOSTIC_NEVER_A_PROOF.
Complex-conjugate positive-height pairs are realified isometrically.
"""
from pathlib import Path
import sys,json,csv,time
import mpmath as mp
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P.parent/'capacity_matrix_2026-11-02'))
from capacity import Erow

def serial(x):
 if isinstance(x,mp.matrix):return [[mp.nstr(x[i,j],95) for j in range(x.cols)] for i in range(x.rows)]
 if isinstance(x,mp.mpf):return mp.nstr(x,95)
 if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
 if isinstance(x,list):return [serial(v) for v in x]
 return x

def rows(z,m,T):
 out=[];sgn=[];labels=[]
 for a in z['critical_line_zeros']:
  g=mp.mpf(a['gamma'])
  if g<T:out.append(Erow(g,m));sgn.append(1);labels.append({'gamma':str(g),'kind':'line'})
 for a in z['off_line_pairs']:
  g=mp.mpf(a['gamma']);d=mp.mpf(a['sigma_right'])-mp.mpf('.5')
  if g<T:
   v=Erow(g+mp.j*d,m)
   for part,sign in [('real',1),('imag',-1)]:
    out.append([mp.sqrt(2)*(mp.re(x) if part=='real' else mp.im(x)) for x in v]);sgn.append(sign);labels.append({'gamma':str(g),'kind':part})
 return mp.matrix(out),sgn,labels

def run(m,path,kappas=None,suffix=""):
 mp.mp.dps=100;t0=time.monotonic();z=json.loads((P/'dh_zeros.json').read_text());src=json.loads(Path(path).read_text());A=mp.matrix(src['A']);d=m+1
 ev=list(map(mp.mpf,src['lambda_']));Om=2*mp.pi*m/mp.log(m);cache={};out=[]
 for k in map(mp.mpf,kappas or ['1','1.2','1.4']):
  E,sign,labels=rows(z,m,k*Om);q=E.rows;r=max(0,d-q)
  if q not in cache:
   U,s,V=mp.svd_r(E,full_matrices=True);rank=min(q,d);sm=s[rank-1];Q=V[rank:,:].T if r else mp.zeros(d,0)
   delta=mp.sqrt(max(mp.eigsy((A*Q).T*(A*Q),eigvals_only=True))) if r else mp.mpf(0)
   beta=max(abs(x) for x in mp.eigsy(Q.T*A*Q,eigvals_only=True)) if r else mp.mpf(0)
   G=2*E.T*E;W=2*E.T*mp.diag(sign)*E;diff=G-W
   svres=mp.norm(E-U[:,:rank]*mp.diag(s)*V[:rank,:]);count=sum(x<delta*mp.mpf('1.000001') for x in ev)
   cache[q]={'q':q,'rank':rank,'dim_J':r,'delta':delta,'compressed_norm':beta,'sigma_min':sm,'sigma_min_squared':sm**2,'twice_sigma_squared':2*sm**2,'lambda_r':ev[r] if r<d else None,'count_delta_plus':count,'count_minus_dim':count-r,'SVD_residual':svres,'sigma_over_svd_residual':sm/svres if svres else None,'E_Q_residual':mp.norm(E*Q) if r else mp.mpf(0),'Q_orthogonality':mp.norm(Q.T*Q-mp.eye(r)) if r else mp.mpf(0),'ordinary_gram_min_on_J_perp':2*sm**2,'signed_zero_form_min':min(mp.eigsy(W,eigvals_only=True)),'negative_metric_correction_norm':max(mp.eigsy(diff,eigvals_only=True)),'A_minus_truncated_signed_norm':max(abs(x) for x in mp.eigsy(A-W,eigvals_only=True)),'labels':labels,'Q':Q,'singular_values':list(s),'weak_right':V[rank-1,:],'eigenvalues':ev}
  out.append({'m':m,'kappa':k,'T':k*Om,**{a:b for a,b in cache[q].items() if a not in ['Q','labels','singular_values','weak_right','eigenvalues']}})
  print('DHquiet',m,str(k),'q',q,'r',r,'delta',mp.nstr(cache[q]['delta'],8),'sigma2',mp.nstr(sm**2,8),flush=True)
 result={'status':'DIAGNOSTIC_NEVER_A_PROOF','m':m,'dps':100,'source':path,'zero_census':'numerical; see dh_zeros.json','rows':out,'cache':cache,'seconds':time.monotonic()-t0}
 (P/f'quiet_m{m}{suffix}.json').write_text(json.dumps(serial(result),indent=2)+'\n')
if __name__=='__main__':run(int(sys.argv[1]),sys.argv[2])
