"""DIAGNOSTIC_NEVER_A_PROOF: literal m8 core and theta ladder, no F/X tail."""
from pathlib import Path
import sys,json,time,hashlib
import mpmath as mp
HERE=Path(__file__).resolve().parent
PARENT=HERE.parent
sys.path.insert(0,str(PARENT))
import core
from ladder import compute_ladder

def compute(dps=100,order=128):
 start=time.monotonic();src=core.setup(dps,order);m=8;L=mp.log(m)
 K,_=src.matrices(L,m);A=src.even(K,m,m);ev,V=mp.eigsy(A)
 hd=[core.theta(L*(y-mp.mpf('.5'))) for y,w in src.nodes]
 h=mp.matrix([mp.sqrt(L)*(1 if n==0 else mp.sqrt(2))*mp.fsum(w*hd[i]*src.trig[n][i][1] for i,(y,w) in enumerate(src.nodes)) for n in range(m+1)])
 Z=mp.norm(h)
 for i in range(m+1):
  pivot=max(range(m+1),key=lambda j:abs(V[j,i]))
  if (i==0 and mp.fdot(V[:,i],h)<0) or (i>0 and V[pivot,i]<0):V[:,i]=-V[:,i]
 atoms=[(n,mp.log(n),core.mangoldt(n)/mp.sqrt(n)) for n in range(2,m+1) if core.mangoldt(n)]
 betas=[core.beta(n,L,atoms) for n in range(m+1)];ds=[mp.mpf(1)]+[mp.sqrt(2)]*m
 pole=[4*mp.sqrt(2)*ds[n]*L**mp.mpf('1.5')*mp.sinh(L/4)/(L*L+16*mp.pi**2*n*n) for n in range(m+1)]
 def row(n,j):return pole[n]*pole[j]+ds[n]*ds[j]/mp.pi*(n*betas[n]-j*betas[j])/(n*n-j*j)
 ctrl=max(abs(row(n,j)-A[n,j]) for n in range(m+1) for j in range(n))
 fmt=lambda x:mp.nstr(x,dps)
 out=dict(status='DIAGNOSTIC_NEVER_A_PROOF',m=m,N=m,dps=dps,order=order,L=fmt(L),Z=fmt(Z),entry_ctrl=fmt(ctrl),lambda_=[fmt(x) for x in ev],a=[fmt(x) for x in V.T*(h/Z)],h=[fmt(x) for x in h],A=[[fmt(x) for x in A[i,:]] for i in range(m+1)],V=[[fmt(x) for x in V[i,:]] for i in range(m+1)],eigen_residual=fmt(mp.norm(A*V-V*mp.diag(ev))),orthogonality_residual=fmt(mp.norm(V.T*V-mp.eye(m+1))),ladder=compute_ladder(m,V,src.nodes,dps),source_sha256={n:hashlib.sha256((PARENT/n).read_bytes()).hexdigest() for n in ('core.py','matrix_core.py','ladder.py')},elapsed=time.monotonic()-start)
 (HERE/f'core_m8_dps{dps}_gl{order}.json').write_text(json.dumps(out,indent=2)+'\n')
 print('complete',dps,order,'entry',ctrl,'seconds',out['elapsed'],flush=True)
def validate():
 mp.mp.dps=160
 a=json.loads((HERE/'core_m8_dps100_gl128.json').read_text());b=json.loads((HERE/'core_m8_dps140_gl160.json').read_text())
 out={'status':'DIAGNOSTIC_NEVER_A_PROOF','sources':['core_m8_dps100_gl128.json','core_m8_dps140_gl160.json']}
 for key in ('A','V','h','lambda_'):
  u=mp.matrix(a[key]);v=mp.matrix(b[key]);e=u-v
  out[key]={'max_absolute_difference':mp.nstr(max(abs(x) for x in e),70),'relative_Frobenius_difference':mp.nstr(mp.norm(e)/mp.norm(v),70)}
 out['eigenvalue_relative_differences']=[mp.nstr(abs(mp.mpf(x)-mp.mpf(y))/abs(mp.mpf(y)),70) for x,y in zip(a['lambda_'],b['lambda_'])]
 u=mp.matrix(a['ladder']['projected_profile_coefficients']);v=mp.matrix(b['ladder']['projected_profile_coefficients'])
 out['ladder_relative_profile_differences']=[mp.nstr(mp.norm(u[:,i]-v[:,i])/mp.norm(v[:,i]),70) for i in range(6)]
 out['controls']=[{key:c[key] for key in ('dps','order','entry_ctrl','eigen_residual','orthogonality_residual')} for c in (a,b)]
 (HERE/'core_m8_validation.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(out,indent=2))
if __name__=='__main__':
 if sys.argv[1]=='validate':validate()
 else:compute(int(sys.argv[1]),int(sys.argv[2]))
