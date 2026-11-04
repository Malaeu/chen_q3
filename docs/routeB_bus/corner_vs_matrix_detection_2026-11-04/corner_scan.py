"""Exhaustive scalar-corner diagnostic, fixed literal source, no RH premise."""
from pathlib import Path
import sys,csv,json,hashlib,time,argparse,importlib.util
sys.path.insert(0,'/workspace/conditioning_deps')
import gmpy2 as g
from flint import arb,acb,ctx
P=Path(__file__).resolve().parent
F=g.mpfr

def setup(maxm,bits=256):
 g.get_context().precision=bits+40;ctx.prec=bits+72
 pi=g.const_pi();zero=F(0);lam=[zero]*(maxm+1);sieve=[True]*(maxm+1)
 for p in range(2,maxm+1):
  if sieve[p]:
   for n in range(p*p,maxm+1,p):sieve[n]=False
   n=p;v=g.log(p)
   while n<=maxm:lam[n]=v;n*=p
 S=[zero]*(maxm+1);W=[zero]*(maxm+1)
 for n in range(2,maxm+1):
  v=lam[n]/g.sqrt(n);S[n]=S[n-1]+v;W[n]=W[n-1]+v*g.log(n)
 tri=F(acb(arb('0.25')).polygamma(1).real.mid().str(int((bits+48)*.30103)+12,radius=False))
 return dict(pi=pi,S=S,W=W,tri=tri,cut=g.exp2(-bits-48),bits=bits)

def source00(m,s):
 L=g.log(m);alpha=F('.5');step=g.exp(-2*L);E=g.exp(-alpha*L);a=alpha;t1=F(0);t2=F(0);terms=0
 while E>s['cut']:
  t1+=E/(a*a);t2+=E/a;E*=step;a+=2;terms+=1
 diag=s['tri']/(2*L)-2*t1/L-2*t2
 c=-g.const_euler()-g.log(8*s['pi'])-s['pi']/2
 z=g.exp(-L/2);tail=2*(g.atanh(z)+g.atan(z))
 prime=2*(s['S'][m-1]-s['W'][m-1]/L)
 pole=32*g.sinh(L/4)**2/L
 return c+diag+tail-prime+pole,L,(1+(1+g.log(L))/(4*L))*2*s['pi']*m/L,terms

def q00(a,gamma,L):
 z=g.mpc(gamma,a);c=2*g.sin(z*L/2)/(g.sqrt(L)*z);return 4*(c*c).real

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--max-m',type=int,default=3000);ap.add_argument('--validate-only',action='store_true');args=ap.parse_args()
 assert json.loads((P/'PRE_RUN_RECEIPT.json').read_text())['confirmed_remote_prediction_commit']
 started=time.process_time();s=setup(max(80,args.max_m));a00,_,_,_=source00(80,s)
 spec=importlib.util.spec_from_file_location('pinned_corner_source',P/'inputs/analytic_source.py');src=importlib.util.module_from_spec(spec);spec.loader.exec_module(src);original,meta=src.build(80,256);difference=abs(a00-original['zeta'][0][0,0]);assert difference<F('1e-60'),str(difference)
 validation=dict(status='PASS_PINNED_SOURCE_CORNER',m=80,bits=256,decimal_working_precision=(256+40)*.30103,absolute_difference=str(difference),source_meta=meta,formula='c+trigamma(1/4)/(2L)-endpoint_corrections+tail-2(S0-S1/L)+32sinh(L/4)^2/L')
 (P/'corner_validation.json').write_text(json.dumps(validation,indent=2)+'\n')
 if args.validate_only:print(json.dumps(validation));return
 gate=json.loads((P/'gate/gate.json').read_text());assert gate['pass'] is True and gate['positive_a_cells_passed']==12 and gate['a0_cells_passed']==4
 values=[('0',F(0)),('1/20',F(1)/20),('1/10',F(1)/10),('1/3',F(1)/3)];gammas=[14,50,200,800]
 summaries={(name,gamma):dict(a=name,gamma=gamma,m_admit=None,m_corner=None,tested_count=0,negative_count=0,minimum=None,minimum_m=None) for name,a in values for gamma in gammas}
 with (P/'corners.csv').open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=['m','L','T','a','gamma','A00','Q00','corner','negative']);w.writeheader()
  for m in range(16,args.max_m+1):
   # Pinned build changes global arithmetic contexts; reset for every scalar cell.
   g.get_context().precision=296;ctx.prec=328
   A,L,T,nt=source00(m,s)
   assert A>0,('unplanted corner control',m,str(A))
   for gamma in gammas:
    if T<=gamma:continue
    for name,a in values:
     Q=q00(a,gamma,L);v=A+Q;negative=bool(v<0);q=summaries[name,gamma]
     if name=='0':assert not negative,('a0cornercontrol',m,gamma,str(v))
     if q['m_admit'] is None:q['m_admit']=m
     if negative and q['m_corner'] is None:q['m_corner']=m
     if q['minimum'] is None or v<F(q['minimum']):q['minimum']=str(v);q['minimum_m']=m
     q['tested_count']+=1;q['negative_count']+=negative
     w.writerow(dict(m=m,L=format(L,'.17g'),T=format(T,'.17g'),a=name,gamma=gamma,A00=format(A,'.20g'),Q00=format(Q,'.20g'),corner=format(v,'.20g'),negative=negative))
   if m%500==0:print(json.dumps(dict(corner_through_m=m)),flush=True)
 out=dict(status='COMPLETE_EXHAUSTIVE_SCALAR_CORNER_SCAN',m_min=16,m_max=args.max_m,bits=256,working_bits=296,controls_a0_pass=True,unplanted_A00_positive=True,cases=list(summaries.values()),CPU_seconds=time.process_time()-started,preregistration=json.loads((P/'PRE_RUN_RECEIPT.json').read_text())['prediction_commit'],script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Finite MPFR diagnostic. A00 computed from exact pinned formulas; no cofinal sign statement or interval-source certificate.')
 (P/'corner_summary.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
