"""Independent arbitrary-precision block/source replay."""
from margins import *
from functools import lru_cache

def validate(world,mesh,n,q,delta,dps):
 mp.mp.dps=dps;h=mp.mpf(1)/mesh;delta=mp.mpf(delta);g0,_=source(world,mp.mpf('6.3'));g=lru_cache(None)(g0)
 saved=json.loads((CORE/f'{world}_mesh{mesh}_dps100.json').read_text()); rr=[mp.mpf(x) for x in saved['r_values']]
 C=mp.matrix([[rr[abs(i-j)] for j in range(n)] for i in range(n)]);L=mp.cholesky(C);d=delta/q
 B=mp.matrix(n,q)
 for i in range(n):
  D=(n-i)*h
  for j in range(q):B[i,j]=g(D+(j+1)*d-h)-g(D+j*d-h)-g(D+(j+1)*d)+g(D+j*d)
 gs=[g(k*d) for k in range(q+1)];fr=[-2*gs[1]]+[2*gs[k]-gs[k-1]-gs[k+1] for k in range(1,q)]
 F=mp.matrix([[fr[abs(i-j)] for j in range(q)] for i in range(q)]);LF=mp.cholesky(F)
 # Exact forward solves preserve all old couplings.
 Y=mp.matrix(n,q)
 for i in range(n):
  for j in range(q):Y[i,j]=(B[i,j]-mp.fsum(L[i,k]*Y[k,j] for k in range(i)))/L[i,i]
 G=Y.T*Y;Li=LF**-1;H=Li*G*Li.T;ev=mp.eigsy(H,eigvals_only=True);mu=1-ev[q-1]
 ff,_=block(float_source(world),np.array(saved['r_values'],float),n,float(h),float(delta),q)
 result=dict(world=world,mesh=mesh,n=n,a=str(n*h),q=q,delta=str(delta),dps=dps,mu_mp=mp.nstr(mu,dps),mu_float=ff['mu'],absolute_error=mp.nstr(abs(mu-mp.mpf(ff['mu'])),30))
 print(json.dumps(result),flush=True);return result

if __name__=='__main__':
 rows=[]
 for world,mesh,n,q,delta,dps in [('zeta',32,192,32,'0.03125',80),('zeta',32,192,32,'.25',80),('dh',32,160,8,'0.03125',80),('plant',32,45,8,'0.03125',80),('zeta',256,64,8,'0.00390625',80),('zeta',256,64,8,'0.00390625',120)]:rows.append(validate(world,mesh,n,q,delta,dps))
 assert max(mp.mpf(r['absolute_error']) for r in rows)<mp.mpf('1e-6')
 (ROOT/'mp_validation.json').write_text(json.dumps(rows,indent=2)+'\n')
