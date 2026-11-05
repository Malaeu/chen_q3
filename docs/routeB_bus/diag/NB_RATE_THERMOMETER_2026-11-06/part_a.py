# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5", "scipy==1.17.0", "mpmath==1.3.0", "matplotlib==3.10.8"]
# ///
"""Finite NB WLS by analytic normal moments; full tail never dropped.
Run: OPENBLAS_NUM_THREADS=4 OMP_NUM_THREADS=4 uv run --no-project part_a.py
Native matrices are ephemeral; all coefficients, numerical checks, and bounds persist.
"""
import argparse,csv,hashlib,json,math,os,subprocess,tempfile,time
from pathlib import Path
import numpy as np
from scipy.linalg import cho_factor,cho_solve,lapack
import mpmath as mp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
HERE=Path(__file__).resolve().parent
GRID=[10,20,50,100,200,500,1000,2000,5000]

def progress(i,n,start,label):
 f=i/n;dt=time.monotonic()-start;j=int(30*f)
 print(f"[{'#'*j}{'.'*(30-j)}] {100*f:5.1f}% ETA {dt*(1-f)/max(f,1e-20):.1f}s {label}",flush=True)

def arithmetic(n):
 mu=np.ones(n+1,dtype=np.int64);mu[0]=0;isprime=np.ones(n+1,dtype=bool);isprime[:2]=False
 psi=np.zeros(n+1);tau=np.zeros(n+1,dtype=np.int64)
 for p in range(2,n+1):
  if isprime[p]:
   isprime[p*p::p]=False
   mu[p::p]*=-1
   if p*p<=n:mu[p*p::p*p]=0
   q=p
   while q<=n:
    psi[q]+=math.log(p)
    if q>n//p:break
    q*=p
  tau[p::p]+=1
 tau[1:]+=1
 return mu,np.cumsum(psi),tau

def compile_native(tmp):
 exe=tmp/'gram_native';subprocess.run(['g++','-O3','-std=c++17','-fopenmp',str(HERE/'part_a_native.cpp'),'-o',str(exe)],check=True);return exe

def native(exe,n,path):
 subprocess.run([str(exe),str(n),str(path)],check=True)
 with path.open('rb') as f:
  d=int(np.fromfile(f,dtype=np.uint32,count=1)[0]);assert d==n-1
  G=np.fromfile(f,dtype=np.float64,count=d*d).reshape(d,d)
  q1=np.fromfile(f,dtype=np.float64,count=n+1)
  assert len(q1)==n+1 and not f.read(1)
 return G,q1

def mp_gram(n):
 # Independent arithmetic implementation of full-H Vasyunin moments at mp30.
 mp.mp.dps=30;kap=mp.log(2*mp.pi)-mp.euler;V={}
 for q in range(1,n+1):
  vals=[mp.mpf(0)]*q;cot=[mp.cot(mp.pi*j/q) for j in range(1,q)]
  for h in range(1,q):
   if math.gcd(h,q)==1:vals[h]=mp.fsum(mp.mpf((h*j)%q)/q*cot[j-1] for j in range(1,q))
  V[q]=vals
 def rho(i,j):
  g=math.gcd(i,j);h=i//g;k=j//g
  return (kap*(mp.mpf(1)/h+mp.mpf(1)/k)/2+mp.mpf(k-h)*mp.log(mp.mpf(h)/k)/(2*h*k)-mp.pi*(V[k][h%k]+V[h][k%h])/(2*h*k))/g
 q1=[mp.mpf(0)]+[rho(i,1) for i in range(1,n+1)]
 G=mp.matrix(n-1)
 for i in range(2,n+1):
  for j in range(2,i+1):G[i-2,j-2]=G[j-2,i-2]=rho(i,j)-q1[i]/j-q1[j]/i+kap/(i*j)
 return G

def periodic_pair(i,j):
 mp.mp.dps=40;p=math.lcm(i,j)
 return mp.fsum(mp.mpf(k%i)/i*mp.mpf(k%j)/j*(mp.digamma(mp.mpf(k+1)/p)-mp.digamma(mp.mpf(k)/p))/p for k in range(1,p))

def monotone(es,tol=1e-10):return all(b<=a+tol for a,b in zip(es,es[1:]))
def optimal(e,ev,eh,tol=1e-10):return e<=min(ev,eh)+tol

def preflight(exe,tmp):
 G,_=native(exe,20,tmp/'preflight.bin');checks={}
 checks['r2_exact_gram_abs_error']=abs(G[0,0]-math.log(2)/4)
 checks['r2_exact_e_abs_error']=abs((1-(math.log(2)/2)**2/G[0,0])-(1-math.log(2)))
 checks['periodic_digamma_pairs']={f'{i},{j}':abs(G[i-2,j-2]-float(periodic_pair(i,j))) for i,j in [(2,3),(3,4),(6,10),(5,17)]}
 assert checks['r2_exact_gram_abs_error']<1e-15 and checks['r2_exact_e_abs_error']<1e-15
 assert max(checks['periodic_digamma_pairs'].values())<1e-15
 assert monotone([.3,.2,.1]) and not monotone([.1,.2])
 assert optimal(.1,.2,.3) and not optimal(.4,.2,.3)
 mu,psi,tau=arithmetic(100);err=0.
 for n in [2,3,5,10,20,50,100]:
  ns=np.arange(1,n+1);a=mu[:n+1][1:]*(1-np.log(ns)/math.log(n));bn=np.longdouble(a)@ (1/np.longdouble(ns));
  for k in range(1,n+1):
   direct=1+np.longdouble(a[1:])@(np.longdouble(k%ns[1:])/ns[1:])
   err=max(err,float(abs(direct-(k*bn-np.longdouble(psi[k])/math.log(n)))))
 assert err<1e-10;checks['J3_BCF_head_max_abs_error']=err;checks['PASS']=True
 (HERE/'part_a_preflight.json').write_text(json.dumps(checks,indent=2)+'\n')
 return checks

def run(maxn,preflight_only):
 start=time.monotonic()
 with tempfile.TemporaryDirectory(prefix='nb_rate_a_') as td:
  tmp=Path(td);exe=compile_native(tmp);preflight(exe,tmp)
  if preflight_only:return
  G,q1=native(exe,maxn,tmp/'gram.bin');mu,psi,tau=arithmetic(maxn)
  results=[];coeff=[];checks=[];small=[];headchecks=[]
  for index,N in enumerate([n for n in GRID if n<=maxn]):
   n=np.arange(2,N+1,dtype=np.float64);Gn=G[:N-1,:N-1].copy();b=np.log(n)/n
   cf=cho_factor(Gn,lower=True,check_finite=False);c=cho_solve(cf,b,check_finite=False)
   e=float(1-b@c);direct=float(1-2*b@c+c@Gn@c)
   assert e>0 and abs(e-direct)<1e-10
   rcond,info=lapack.dpocon(cf[0],float(np.linalg.norm(Gn,1)),uplo='L');assert info==0
   g=np.gcd(n.astype(np.int64)[:,None],n.astype(np.int64)[None,:]).astype(float)
   meanr=(n-1)/(2*n);meanG=np.outer(meanr,meanr)+(g*g-1)/(12*np.outer(n,n));del g
   c1=float(np.sum(abs(c)));T=float(n@abs(c));lambda0=1/(4*N*(N+1)*float(np.sum(tau[2:N+1]**2)))
   # K-row WLS moments are analytically aggregated, no K-by-N allocation.
   K=max(10**20,int(math.ceil(4000*(1+c1)**2/e)));D=float((K+1)*(K+2))
   mean_res=float(1-2*meanr@c+c@meanG@c)
   periodic_error=(2*T+T*T)/D
   omitted_gradient=float(np.linalg.norm(meanr-meanG@c))/(K+1)+float(np.linalg.norm(n))*(1+T)/D
   stationarity=float(np.linalg.norm(Gn@c-b))
   # Arithmetic residual shown separately; not a rigorous interval enclosure.
   finite_opt_gap=(omitted_gradient+stationarity)**2/lambda0
   finite_delta=max(0.,mean_res)/(K+1)+periodic_error+omitted_gradient**2/lambda0
   tail=(1+c1)**2/(K+1);assert tail<1e-3*e
   Gk=Gn-meanG/(K+1);bk=b-meanr/(K+1);targetk=1-1/(K+1)
   ck=cho_solve(cho_factor(Gk,lower=True,check_finite=False),bk,check_finite=False)
   ek=float(targetk-bk@ck);assert abs(ek-e)<1e-10
   a=mu[2:N+1]*(1-np.log(n)/math.log(N));ev=float(1+2*b@a+a@Gn@a)
   m1prev=np.sum(np.longdouble(mu[1:N])/np.arange(1,N,dtype=np.longdouble),dtype=np.longdouble)
   ch=-mu[2:N+1].astype(np.float64);ch[-1]=float(N*m1prev);eh=float(1-2*b@ch+ch@Gn@ch)
   assert optimal(e,ev,eh)
   # Full requested head identities at every A-grid N, not only preflight N.
   ns=np.arange(1,N+1,dtype=np.longdouble)
   aa=np.longdouble(mu[1:N+1])*(1-np.log(ns)/np.log(np.longdouble(N)))
   bn_ld=np.sum(aa/ns,dtype=np.longdouble);maxh=0.;maxv=0.
   hh=np.longdouble(ch)
   for k in range(1,N+1):
    rr=np.longdouble(k%np.arange(2,N+1))/ns[1:]
    rv=1+aa[1:]@rr
    maxv=max(maxv,float(abs(rv-(k*bn_ld-np.longdouble(psi[k])/np.log(np.longdouble(N))))))
    if k<N:maxh=max(maxh,float(abs(hh@rr-1)))
   assert maxh<=1e-12 and maxv<=1e-10
   headchecks.append(dict(N=N,H_N_max_abs_error=maxh,BCF_max_abs_error=maxv,J3=True))
   stable_head_gap=float((ch-c)@Gn@(ch-c));stable_bcf_gap=float((-a-c)@Gn@(-a-c))
   assert abs(stable_head_gap-(eh-e))<1e-9 and abs(stable_bcf_gap-(ev-e))<1e-9
   R0=float(1-mp.euler);bn=float(1+np.sum(a/n));cross=R0+float(a@(q1[2:N+1]-(math.log(2*math.pi)-float(mp.euler))/n))
   evraw=ev+2*bn*cross+bn*bn*(math.log(2*math.pi)-float(mp.euler))
   row=dict(N=N,e_N=e,e_logN=e*math.log(N),E_V_centered=ev,E_V_logN=ev*math.log(N),threshold_ratio=2*e*math.log(N),E_head=eh,E_BCF_uncentered_global=evraw,K=str(K),tail_bound=tail,tail_relative=tail/e,finite_WLS_estimate=ek,finite_optimum_vs_infinite_bound=finite_delta,periodic_tail_remainder_bound=periodic_error,finite_WLS_stationarity_gap_bound=finite_opt_gap,condition_1_estimate=1/rcond,stationarity_norm2=stationarity,objective_evaluation_disagreement=abs(e-direct),coefficient_l1=c1,lambda_head_lower_bound=lambda0)
   results.append(row)
   for j,x in enumerate(c,2):coeff.append(dict(N=N,n=j,c=float(x)))
   checks.append(dict(N=N,J2_optimality=True,BCF_upper_gap=ev-e,head_upper_gap=eh-e))
   progress(index+1,len([n for n in GRID if n<=maxn]),start,'A float64 solves')
  assert monotone([r['e_N'] for r in results])
  cap=min(200,maxn);M=mp_gram(cap)
  for N in [n for n in GRID if n<=cap]:
   A=M[:N-1,:N-1];bb=mp.matrix([mp.log(i)/i for i in range(2,N+1)]);cm=mp.lu_solve(A,bb);em=1-(bb.T*cm)[0]
   r=next(x for x in results if x['N']==N);diff=abs(float(em)-r['e_N']);assert diff<1e-10
   small.append(dict(N=N,mp_dps=30,e_N_mp=str(em),float64_e=r['e_N'],absolute_difference=diff,max_gram_difference=float(max(abs(A[i,j]-mp.mpf(float(G[i,j]))) for i in range(N-1) for j in range(N-1)))))
   progress(N,cap,start,'A mp30 crosscheck')
  writecsv('part_a_head_identity.csv',headchecks);writecsv('part_a_results.csv',results);writecsv('part_a_coefficients.csv',coeff);writecsv('part_a_mp30.csv',small);writecsv('part_a_judges.csv',checks)
  es=np.array([r['e_N'] for r in results]);Ls=np.log([r['N'] for r in results]);evs=np.array([r['E_V_centered'] for r in results]);xs=np.array([r['N'] for r in results]);
  fig,ax=plt.subplots(figsize=(9,5));ax.semilogx(xs,es*Ls,'o-',label='optimal e_N log N');ax.semilogx(xs,evs*Ls,'s-',label='centered BCF error × log N');ax.axhline(.5,color='red',ls='--',label='sufficient threshold 1/2');ax.axhline(float(2+mp.euler-mp.log(4*mp.pi)),color='gray',ls=':',label='BCF conditional asymptotic constant (uncentered)');ax.set(xlabel='N',ylabel='squared error × log N',title='Finite NB rate diagnostics');ax.grid(True,alpha=.3);ax.legend();fig.tight_layout();fig.savefig(HERE/'part_a_rate.png',dpi=170);plt.close(fig)
  summary=dict(J1=True,J2=True,J3_BCF=True,mp30_crosschecks=True,max_n=maxn,seconds=time.monotonic()-start,preregistered_scores={'A1':'HIT' if all(r['e_logN']<=.5 for r in results if r['N']>=50) else 'MISS','A2':'HIT' if any(r['N']==1000 and .03<=r['e_logN']<=.15 for r in results) else ('MISS' if maxn>=1000 else 'NOT_RUN'),'A3':'HIT' if monotone([r['E_V_logN'] for r in results],1e-12) and .04<=results[-1]['E_V_logN']<=.10 else 'MISS'},A3_monotonic=monotone([r['E_V_logN'] for r in results],1e-12),A3_endpoint_in_band=.04<=results[-1]['E_V_logN']<=.10,arithmetic_scope='point arithmetic, truncation-only analytic bounds; not outward-rounded intervals',method='Vasyunin full Gram + periodic-tail aggregated finite-K normal equations')
  (HERE/'part_a_summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary),flush=True)

def writecsv(name,rows):
 with (HERE/name).open('w') as f:
  w=csv.DictWriter(f,fieldnames=list(rows[0]),lineterminator='\n');w.writeheader();w.writerows(rows)
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--max-n',type=int,default=5000,choices=[10,20,50,100,200,500,1000,2000,5000]);ap.add_argument('--preflight-only',action='store_true');ar=ap.parse_args();run(ar.max_n,ar.preflight_only)
