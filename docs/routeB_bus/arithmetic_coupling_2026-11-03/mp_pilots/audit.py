"""Three-window MP epsilon sensitivity diagnostic; not interval certification."""
from pathlib import Path
import sys,csv,json,time,os
import mpmath as mp
P=Path(__file__).resolve().parent;sys.path.insert(0,str(P.parent/'source'));import split
mp.mp.dps=120
fmt=lambda x:mp.nstr(x,115)
def convert(A):return mp.matrix([[mp.mpf(str(v))for v in row]for row in A])
def mgs(rows):
 us=[];ratios=[]
 for row in rows:
  v=mp.matrix(row);n0=mp.norm(v)
  for _ in range(2):
   for u in us:v-=u*mp.fdot(u,v)
  n=mp.norm(v);assert n>0;ratios.append(n/n0);us.append(v/n)
 return mp.matrix([[us[k][j]for k in range(len(us))]for j in range(len(us[0]))]),min(ratios)
def quiet(A,m,return_state=False):
 d=m+1;L=mp.log(m);T=2*mp.pi*m/L;gam=[mp.mpf(x['gamma'])for x in csv.DictReader(Path(os.environ.get('QUIET_ZETA',str(P.parent/'source_inputs/zeta_zeros.csv'))).open())if mp.mpf(x['gamma'])<T];q=len(gam);r=d-q;ds=[mp.mpf(1)]+[mp.sqrt(2)]*m
 E=mp.matrix([[2*ds[j]*t*mp.sin(t*L/2)/(mp.sqrt(L)*(t*t-(2*mp.pi*j/L)**2))for j in range(d)]for t in gam]);weights=[]
 for j in range(d):
  v=(-1)**(m-j)*(2/ds[j] if j else 1)/(mp.factorial(m-j)*mp.factorial(m+j))
  for t in gam:v*=j*j-(t*L/(2*mp.pi))**2
  weights.append(v)
 scale=max(abs(v)for v in weights);weights=[v/scale for v in weights];rows=[[weights[j]*(mp.mpf(j*j)/(m*m))**k for j in range(d)]for k in range(r)];Q,piv=mgs(rows);D=Q.T*A*Q;ev=mp.eigsy(D,eigvals_only=True)
 result=dict(m=m,q=q,r=r,T=fmt(T),minimum_quiet_lambda=fmt(ev[0]),maximum_quiet_lambda=fmt(ev[ev.rows-1]),E_Q_max_entry=fmt(max(abs(v)for v in E*Q)),Q_orthogonality_max_entry=fmt(max(abs(v)for v in Q.T*Q-mp.eye(r))),minimum_relative_MGS_pivot=fmt(piv),source_floor_status='empirical400bit source floor ~1e-114; no interval bound; compare displayed minimum to this floor')
 if return_state:
  ee,V=mp.eigsy(D);return result,Q,D,ee,V
 return result
def run(m):
 start=time.monotonic();s=split.build(m,256)['zeta'];C=convert(s['C']);B=convert(s['B']);A=C+B;rows=[]
 for exponent in [20,40,60,80,100]:
  eps=mp.mpf(10)**(-exponent);G=A+eps*mp.eye(m+1)
  try:L=mp.cholesky(G)
  except ValueError:
   rows.append(dict(m=m,epsilon=fmt(eps),status='CHOLESKY_FAILED_SOURCE_SIGN_UNRESOLVED'));continue
  Li=L**-1;H=Li*B*Li.T;H=(H+H.T)/2;ev=mp.eigsy(H,eigvals_only=True);hmin=ev[0];hmax=ev[ev.rows-1];lower=-1/hmax if hmax>0 else -mp.inf;upper=-1/hmin if hmin<0 else mp.inf
  chol=max(abs(v)for v in G-L*L.T);row=dict(m=m,epsilon=fmt(eps),status='MP_NUMERICAL_DIAGNOSTIC',hmin=fmt(hmin),hmax=fmt(hmax),u_minus_minus_1=fmt(lower),u_plus_minus_1=fmt(upper),width=fmt(upper-lower),width_over_epsilon=fmt((upper-lower)/eps),cholesky_max_entry_residual=fmt(chol));rows.append(row);print(m,exponent,'offsets',fmt(lower),fmt(upper),flush=True)
 q=quiet(A,m);out=dict(status='DIAGNOSTIC_NEVER_A_PROOF',m=m,source_bits=400,source_GL_order=256,panels=8,mp_dps=120,rows=rows,quiet=q,seconds=time.monotonic()-start);(P/f'm{m}.json').write_text(json.dumps(out,indent=2)+'\n');print('DONE',m,'seconds',out['seconds'],'quietmin',q['minimum_quiet_lambda'],flush=True)
if __name__=='__main__':
 for m in [16,24,40]:run(m)
