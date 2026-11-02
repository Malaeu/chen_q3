"""DIAGNOSTIC_NEVER_A_PROOF: fresh high-precision literal CCM eigenvectors."""
from pathlib import Path
import sys,json,hashlib,time
import mpmath as mp
OUT=Path(__file__).resolve().parent
BASE=OUT.parents[2]
sys.path.insert(0,str(BASE))
import core

def build(m,dps,order):
 start=time.monotonic();src=core.setup(dps,order);L=mp.log(m)
 K,_=src.matrices(L,m);A=src.even(K,m,m);ev,V=mp.eigsy(A)
 hd=[core.theta(L*(y-mp.mpf('.5'))) for y,w in src.nodes]
 h=mp.matrix([mp.sqrt(L)*(1 if n==0 else mp.sqrt(2))*mp.fsum(w*hd[i]*src.trig[n][i][1] for i,(y,w) in enumerate(src.nodes)) for n in range(m+1)])
 for i in range(m+1):
  pivot=max(range(m+1),key=lambda j:abs(V[j,i]))
  if (i==0 and mp.fdot(V[:,i],h)<0) or (i>0 and V[pivot,i]<0):V[:,i]=-V[:,i]
 fmt=lambda x:mp.nstr(x,dps)
 data=dict(status='DIAGNOSTIC_NEVER_A_PROOF',m=m,N=m,dps=dps,order=order,L=fmt(L),lambda_=[fmt(x) for x in ev],A=[[fmt(x) for x in A[i,:]] for i in range(m+1)],V=[[fmt(x) for x in V[i,:]] for i in range(m+1)],h=[fmt(x) for x in h],eigen_residual=fmt(mp.norm(A*V-V*mp.diag(ev))),orthogonality_residual=fmt(mp.norm(V.T*V-mp.eye(m+1))),source_sha256={n:hashlib.sha256((BASE/n).read_bytes()).hexdigest() for n in ('core.py','matrix_core.py')},profile_columns=list(range(8))+[m//2,m-2],sign_convention='ground positive theta overlap; others largest modal coordinate positive',elapsed=time.monotonic()-start)
 p=OUT/f'core_m{m}_dps{dps}_gl{order}.json';p.write_text(json.dumps(data,indent=2)+'\n');print(p.name,'seconds',data['elapsed'],flush=True)

def validate():
 mp.mp.dps=240;rows=[]
 for m in (16,20,24):
  a=json.loads((OUT/f'core_m{m}_dps180_gl160.json').read_text());b=json.loads((OUT/f'core_m{m}_dps220_gl192.json').read_text())
  r={'m':m,'status':'DIAGNOSTIC_NEVER_A_PROOF','controls':[{k:c[k] for k in ('dps','order','eigen_residual','orthogonality_residual')} for c in (a,b)]}
  for key in ('A','V'):
   u=mp.matrix(a[key]);v=mp.matrix(b[key]);r[key]={'max_absolute_difference':mp.nstr(max(abs(x) for x in u-v),90),'relative_Frobenius_difference':mp.nstr(mp.norm(u-v)/mp.norm(v),90)}
  r['eigenvalue_relative_differences']=[mp.nstr(abs(mp.mpf(x)-mp.mpf(y))/abs(mp.mpf(y)),90) for x,y in zip(a['lambda_'],b['lambda_'])]
  U=mp.matrix(a['V']);V=mp.matrix(b['V']);r['eigenvector_L2_differences']=[mp.nstr(mp.norm(U[:,i]-V[:,i]),90) for i in range(m+1)]
  rows.append(r)
 (OUT/'core_validation.json').write_text(json.dumps(rows,indent=2)+'\n')
 print('validation complete',flush=True)
if __name__=='__main__':
 if sys.argv[1]=='validate':validate()
 else:
  m,dps,order=map(int,sys.argv[1:]);build(m,dps,order)
