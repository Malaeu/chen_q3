"""Native inverse-evaluation scan with GMP dense solves. NOT Weyl radii.
DIAGNOSTIC_NEVER_A_PROOF. Input zeros and finite inertia remain numerical.
"""
from pathlib import Path
import mpmath as mp
import json,csv,subprocess,time,sys,hashlib,concurrent.futures,os
from curve import coefficients
from exact_label_records import annotate
P=Path(__file__).resolve().parent;IN=Path(sys.argv[1]) if len(sys.argv)>1 else P.parent/'inputs'
OUT=P/'native_cells';OUT.mkdir(exist_ok=True)
DPS=int(os.environ.get('SCREW_DPS','220'));ORDER=int(os.environ.get('SCREW_ORDER','256'));BITS=int(os.environ.get('SCREW_BITS','768'))
mp.mp.dps=DPS
GN=None;BOTH=None;ZS=None;DZ=None

def gauss(n):
 out=[]
 for k in range(1,n//2+1):
  z=mp.cos(mp.pi*(mp.mpf(k)-mp.mpf('.25'))/(mp.mpf(n)+mp.mpf('.5')))
  for iteration in range(40):
   p0=mp.mpf(1);p1=z
   for j in range(2,n+1):p0,p1=p1,((2*j-1)*z*p1-(j-1)*p0)/j
   dp=n*(z*p1-p0)/(z*z-1);new=z-p1/dp
   if new==z:break
   z=new
  p0=mp.mpf(1);p1=z
  for j in range(2,n+1):p0,p1=p1,((2*j-1)*z*p1-(j-1)*p0)/j
  dp=n*(z*p1-p0)/(z*z-1);w=2/((1-z*z)*dp*dp);out.extend([(-z,w),(z,w)])
 out.sort();assert abs(sum(w for z,w in out)-2)<mp.mpf(10)**(-DPS+8)
 return out

def initialize():
 global GN,BOTH,ZS,DZ
 # Compute roots once; keep every source quadrature node in physical precision.
 roots=gauss(ORDER);GN=[((mp.mpf(panel)+(z+1)/2)/8,w/16,mp.cos(2*mp.pi*(panel+(z+1)/2)/8),mp.sin(2*mp.pi*(panel+(z+1)/2)/8)) for panel in range(8) for z,w in roots]
 BOTH={world:coefficients(260,world) for world in ['zeta','dh']}
 ZS=[mp.mpf(r['gamma']) for r in csv.DictReader((IN/'zeros.csv').open())]
 DZ=json.loads((IN/'dh_zeros_extended.json').read_text())

def fmt(x):return mp.nstr(x,DPS)
def prepare(world,m):
 L=mp.log(m);sqrtL=mp.sqrt(L);T=mp.mpf('1.1')*2*mp.pi*m/L;alpha=mp.mpf('.5') if world=='zeta' else mp.mpf('1.5')
 rows=[]
 if world=='zeta':events=[(g,mp.mpf(0)) for g in ZS if g<T]
 else:events=sorted([(mp.mpf(a['gamma']),mp.mpf(0)) for a in DZ['critical_line_zeros'] if mp.mpf(a['gamma'])<T]+[(mp.mpf(a['gamma']),mp.mpf(a['sigma_right'])-mp.mpf('.5')) for a in DZ['off_line_pairs'] if mp.mpf(a['gamma'])<T])
 if world=='dh' and mp.mpf(os.environ.get('SCREW_NODE_PERTURB','0')):
  ep=mp.mpf(os.environ['SCREW_NODE_PERTURB']);events=[(g+ep*((-1)**i),de+ep*((-1)**i)/2 if de else de) for i,(g,de) in enumerate(events)]
 for gamma,eta in events:
  z=gamma+mp.j*eta;v=2*z*mp.sin(z*L/2)/sqrtL
  if not eta:rows.append('0 '+ ' '.join(map(fmt,[gamma*gamma,0,mp.re(v),0])))
  else:
   for kind in [1,2]:rows.append(str(kind)+' '+' '.join(map(fmt,[mp.re(z*z),mp.im(z*z),mp.re(v),mp.im(v)])))
 q=len(rows);b=BOTH[world];atoms=[]
 for n in range(2,m):
  if b[n]:
   y=mp.log(n)/L;atoms.append(' '.join(map(fmt,[y,mp.cos(2*mp.pi*y),mp.sin(2*mp.pi*y),b[n]/mp.sqrt(n)])))
 c=-mp.euler-mp.log(8*mp.pi)-mp.pi/2 if world=='zeta' else -mp.euler-mp.log(8*mp.pi/5)+mp.pi/2
 aa=mp.exp(-L/2);tail=mp.atanh(aa)+(mp.atan(aa) if world=='zeta' else -mp.atan(aa));s2=mp.sqrt(2)
 txt=[f'{m} {q} {len(GN)} {len(atoms)} {int(world=="zeta")}', ' '.join(map(fmt,[L,sqrtL,1/mp.pi,s2,(2*mp.pi/L)**2,c,2*tail]))]
 for y,w,co,si in GN:txt.append(' '.join(map(fmt,[y,co,si,L*w*mp.exp(-alpha*L*y)/(-mp.expm1(-2*L*y))])))
 txt.extend(atoms)
 pole=[4*s2*(1 if n==0 else s2)*L**mp.mpf('1.5')*mp.sinh(L/4)/(L*L+16*mp.pi**2*n*n) for n in range(m+1)]
 txt.append(' '.join(map(fmt,pole)));txt.extend(rows)
 for n in range(m+1):
  dn=1 if n==0 else s2;wv=(2*mp.pi*n/L)**2
  queries=[dn/sqrtL]+[dn*2*y*mp.sinh(y*L/2)/(sqrtL*(y*y+wv)) for y in [mp.mpf('.5'),mp.mpf(1),mp.mpf(2)]]
  txt.append(' '.join(map(fmt,queries)))
 return '\n'.join(txt)+'\n',T,q

def run_case(case):
 world,m=case
 suffix=os.environ.get('SCREW_SUFFIX','');existing=OUT/f'{world}_m{m}_dps{DPS}_gl{ORDER}{suffix}.json'
 if existing.exists() and os.environ.get('SCREW_FORCE','0')!='1':return json.loads(existing.read_text())
 start=time.time();text,T,q=prepare(world,m);exe=Path(os.environ.get('SCREW_EXE',str(P/'native')))
 proc=subprocess.run([str(exe),str(BITS)],input=text,text=True,capture_output=True)
 common={'status':'DIAGNOSTIC_NEVER_A_PROOF','world':world,'m':m,'q':q,'kappa':'1.1','T':fmt(T),'L':fmt(mp.log(m)),'source_dps':DPS,'source_order':ORDER,'bits':BITS,'input_sha256':hashlib.sha256(text.encode()).hexdigest(),'query_convention':['physical_endpoint','Fourier_i/2','Fourier_i','Fourier_2i'],'geometry_label':'ALGEBRAIC_INVERSE_FORM_NOT_A_WEYL_RADIUS','zero_node_precision':'pinned numerical census; no interval zero proof','node_perturbation':os.environ.get('SCREW_NODE_PERTURB','0'),'node_perturbation_applied':bool(world=='dh' and mp.mpf(os.environ.get('SCREW_NODE_PERTURB','0')))}
 if proc.returncode:
  result={**common,'numerical_status':'UNRESOLVED_ZERO_PIVOT_OR_RANK_FAILURE','returncode':proc.returncode,'stderr':proc.stderr}
 else:
  result={**common,**json.loads(proc.stdout),'numerical_status':'SINGLE_PRECISION_DIAGNOSTIC_REQUIRES_CONTROLS'}
  kval=list(map(mp.mpf,result['K']));result['signed_reciprocal_proxy']=[fmt(1/(y*K)) if K else None for y,K in zip([mp.mpf('.5'),mp.mpf(1),mp.mpf(2)],kval[1:])]
  result['reciprocal_proxy_squared']=[fmt((1/(y*K))**2) if K else None for y,K in zip([mp.mpf('.5'),mp.mpf(1),mp.mpf(2)],kval[1:])]
  bn=BOTH[world][m];result['b_m']=fmt(bn);result['birth_source_coefficient']=fmt(-2*bn/mp.sqrt(m));result['birth_inverse_kernel_derivative_kinks']=[fmt(2*bn/mp.sqrt(m)*mp.mpf(x)**2) for x in result['endpoint_cross']]
 result=annotate(result)
 result['seconds']=time.time()-start
 (OUT/f'{world}_m{m}_dps{DPS}_gl{ORDER}{suffix}.json').write_text(json.dumps(result,indent=2)+'\n')
 print(world,m,'q',q,'neg',result.get('negative_pivots'),'Kendpoint',result.get('K',[None])[0],'seconds',round(result['seconds'],2),flush=True)
 return result

if __name__=='__main__':
 # Use fork to share the immutable high-precision quadrature and source constants.
 initialize();print('INITIALIZED',DPS,ORDER,flush=True)
 ms=[int(x) for x in sys.argv[2:]] if len(sys.argv)>2 else list(range(20,241))
 cases=[(w,m) for m in ms for w in ['zeta','dh']]
 workers=int(os.environ.get('SCREW_WORKERS','3'))
 if workers==1:
  for c in cases:run_case(c)
 else:
  with concurrent.futures.ProcessPoolExecutor(max_workers=workers) as pool:list(pool.map(run_case,cases))
