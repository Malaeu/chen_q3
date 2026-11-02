"""Arb interval evaluation of the unchanged dh_matrix.py scalar Rayleigh form.

No interval eigenvalue claim: frozen decimal witness, exact-source integration.
"""
from pathlib import Path
import json,sys,time,os,hashlib
import mpmath as mp
import flint
from flint import arb,acb,ctx
P=Path(__file__).resolve().parent
INPUT=Path(os.environ.get('DH_INPUTS',str(P.parent.parent)))
SOURCE_SHA256='9554c27549fc0970391c06026d8bfb402ab1cfa3b2f1db3c0db6deeb92a39f00'

def main(m):
 ctx.prec=600;mp.mp.dps=170;start=time.monotonic()
 actual_source_sha256=hashlib.sha256((INPUT/'dh_matrix.py').read_bytes()).hexdigest()
 if actual_source_sha256!=SOURCE_SHA256:raise RuntimeError('changed dh_matrix.py source')
 path=next((INPUT/'matrix_cells').glob(f'dh_m{m}_dps120_*.json'))
 src=json.loads(path.read_text());A=mp.matrix(src['A']);ev,V=mp.eigsy(A)
 # Decimal witness is now fixed. Its rounding need not preserve eigvector status.
 vs=[mp.nstr(V[n,0],165) for n in range(m+1)]
 v=[arb(x) for x in vs];L=arb(m).log();pi=arb.pi();norm=sum(x*x for x in v)
 tau=((10-2*arb(5).sqrt()).sqrt()-2)/(arb(5).sqrt()-1)
 aa=[arb(0),arb(1),tau,-tau,arb(-1)];bb=[arb(0)]*(m+1)
 for n in range(2,m+1):bb[n]=aa[n%5]*arb(n).log()-sum(bb[d]*aa[(n//d)%5] for d in range(2,n) if n%d==0)
 C=[2*x*x for x in v];S=[arb(0)]*(m+1);ds=[arb(1)]+[arb(2).sqrt()]*m
 for n in range(1,m+1):S[n]-=v[n]*v[n]/(pi*n)
 for i in range(m+1):
  for j in range(i+1,m+1):
   t=2*v[i]*v[j]*ds[i]*ds[j]/pi/(i*i-j*j)
   S[j]+=t*j;S[i]-=t*i
 def corr(s):
  return sum(C[n]*(1-s/L)*(2*pi*n*s/L).cos()+S[n]*(2*pi*n*s/L).sin() for n in range(m+1))
 prime=sum(bb[n]/arb(n).sqrt()*corr(arb(n).log()) for n in range(2,m))
 # psi(3/4) = -gamma + pi/2 -3log2, exact known identity.
 constant=(arb(5)/pi).log()-arb.const_euler()+pi/2-3*arb(2).log()
 a=(-L/2).exp();tail=a.atanh()-a.atan()
 # Removable cancellation divided by s is evaluated using entire sinc/cosc.
 def integrand(s,analytic):
  s=acb(s);z=s/L
  # (2norm-Q(s))/s = sum C_n/L*cos + C_n*(1-cos)/s -S_n*sin/s.
  total=acb(0)
  for n in range(m+1):
   om=2*acb(pi)*n/acb(L);x=om*s
   # 1-cos x = 2sin(x/2)^2, sin x / s = om*sinc(x).
   sinc=lambda y:y.sinc()
   total+=acb(C[n])/acb(L)*x.cos()+acb(C[n])*om*om*s/2*sinc(x/2)**2-acb(S[n])*om*sinc(x)
  # s*j(s)=exp(-s/2) * s/(exp(s)-exp(-s)) = exp(-s/2)/(2*sinhc(s)).
  sinhc=(acb(0,1)*s).sinc()
  return (-s/2).exp()*total/(2*sinhc)
 # The integrand is analytic in |Im s|<pi; split into short subintervals.
 H=acb(0)
 for p in range(16):
  H+=acb.integral(integrand,acb(L*p/16),acb(L*(p+1)/16),abs_tol=arb('1e-150'),rel_tol=arb('1e-140'),deg_limit=240,eval_limit=100000)
 H=H.real+2*norm*tail
 numerator=constant*norm+H-prime;ray=numerator/norm
 out=dict(status='ARB_RAYLEIGH_INTERVAL',m=m,precision_bits=ctx.prec,python_flint_version=flint.__version__,source_commit='d26831357b6cb3b2b7d4a569d2031e454952b246',source_sha256=actual_source_sha256,matrix_witness_source=str(path),matrix_witness_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),witness=vs,witness_semantics='fixed decimal rationals, outward enclosed on Arb conversion; eigenvector accuracy not assumed by certificate',norm=str(norm),constant=str(constant),arch_including_infinite_tail=str(H),arithmetic_all_integers=str(prime),numerator=str(numerator),rayleigh=str(ray),strict_negative=bool(ray<0),integration=dict(method='acb.integral',subintervals=16,abs_tol='1e-150',rel_tol='1e-140',deg_limit=240,eval_limit=100000,removable_endpoint='entire sinc form'),claim='exists a source-operator vector with strictly negative Rayleigh quotient; not an interval eigenpair certificate',seconds=time.monotonic()-start)
 if m in (51,55):
  lo,hi={51:('-1.326858e-47','-1.326857e-47'),55:('-0.663921','-0.663920')}[m]
  assert arb(lo)<ray and ray<arb(hi)<0
  out.update(coarse_enclosing_interval=[lo,hi],certified_upper=hi,coarse_enclosure_checked_with_arb=True)
 (P/f'rayleigh_m{m}.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='witness'}),flush=True)
 if not ray<0:raise RuntimeError('negative upper not established')
if __name__=='__main__':main(int(sys.argv[1]))
