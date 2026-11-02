"""DIAGNOSTIC_NEVER_A_PROOF: positive-zero sampling Gram matrices, no tail proof."""
from pathlib import Path
import sys,json,csv,hashlib,time
import mpmath as mp
OUT=Path(__file__).resolve().parent;BASE=OUT.parent

def Erow(t,m):
 L=mp.log(m);b=L/2;row=[]
 for n in range(m+1):
  d=1 if n==0 else mp.sqrt(2);omega=2*mp.pi*n/L
  if abs(t-omega)<mp.mpf('1e-80') or abs(t+omega)<mp.mpf('1e-80'):
   v=d*(-1)**n*b/mp.sqrt(L)*(mp.sinc((t-omega)*b)+mp.sinc((t+omega)*b))
  else:v=2*d*t*mp.sin(t*b)/(mp.sqrt(L)*(t*t-omega*omega))
  row.append(v)
 return row

def serial(x):
 if isinstance(x,mp.matrix):return [[mp.nstr(x[i,j],180) for j in range(x.cols)] for i in range(x.rows)]
 if isinstance(x,mp.mpf):return mp.nstr(x,180)
 if isinstance(x,list):return [serial(v) for v in x]
 if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
 return x

def compute(m):
 start=time.monotonic();mp.mp.dps=180;d=m+1
 zs=[mp.mpf(r['gamma']) for r in csv.DictReader((OUT/'zeros.csv').open())];zs=[z for z in zs if z<=400]
 source=BASE/f'lowcluster_2026-11-02/ladder_limit/identify/zero_height_local/core_m{m}_dps180_gl160.json'
 s=json.loads(source.read_text());A=mp.matrix(s['A']);V=mp.matrix(s['V']);ae=list(map(mp.mpf,s['lambda_']))
 E=mp.matrix([Erow(z,m) for z in zs]);G=E.T*E;g,U=mp.eigsy(G)
 residual=A-2*G;re=mp.eigsy(residual,eigvals_only=True);single=mp.eigsy(A-G,eigvals_only=True)
 tol=mp.eps*max(mp.mpf(1),mp.norm(G))*d*100
 resolved=[i for i in range(d) if g[i]>tol]
 W=mp.matrix(E.rows,len(resolved))
 for k,i in enumerate(resolved):W[:,k]=(E*U[:,i])/mp.sqrt(g[i])
 overlap=V.T*U;overlap=mp.matrix([[overlap[i,j]**2 for j in range(d)] for i in range(d)])
 prefixes=set(range(1,min(40,len(zs))+1))|{4,8,12,16,24,32,48,64,96,128,d-1,d,d+1,len(zs)}
 prefixes|={sum(z<=height for z in zs) for height in range(50,401,50)}
 prefixes=sorted(q for q in prefixes if 0<q<=len(zs));prefixrows=[]
 GG=mp.zeros(d);lastq=0
 for q in prefixes:
  for k in range(lastq,q):
   v=E[k,:].T;GG+=v*v.T
  lastq=q
  ev,Uq=mp.eigsy(GG);qtol=mp.eps*max(mp.mpf(1),mp.norm(GG))*d*100;null=max(0,d-q)
  classes=['structural_null_rank_bound' if i<null else ('resolved_positive' if ev[i]>qtol else 'numerically_unresolved') for i in range(d)]
  # Retain raw signed roundoff; never treat structural null directions as resolved.
  metrics={'q':q,'height':zs[q-1],'U':Uq,'overlap_squared_with_full_G_basis':mp.matrix([[(U[:,i].T*Uq[:,j])[0]**2 for j in range(d)] for i in range(d)]),'structural_nullity_lower_bound':null,'resolution_tolerance':qtol,'resolution_classes':classes,'g_eigenvalues':list(ev),'relative_eigenvalue_difference_from_full':[abs(ev[i]-g[i])/abs(g[i]) if g[i] else None for i in range(d)],'norm_difference_from_full_G':mp.norm(GG-G)}
  for B in (2,4,8):
   mu=mp.mpf(m)**(-B)
   metrics[f'G_count_B{B}']=sum(abs(x)<mu for x in ev);metrics[f'2G_count_B{B}']=sum(abs(2*x)<mu for x in ev);metrics[f'A_count_B{B}']=sum(abs(x)<mu for x in ae)
  if q not in {sum(z<=height for z in zs) for height in (100,200,300,350,400)}:
   metrics.pop('U');metrics.pop('overlap_squared_with_full_G_basis')
  prefixrows.append(metrics)
  print('prefix',m,q,flush=True)
 out={'status':'DIAGNOSTIC_NEVER_A_PROOF','m':m,'N':m,'dimension':d,'dps':180,'matrix_source_order':160,'height_cutoff':400,'positive_zero_count':len(zs),'normalization':'unweighted positive-zero E rows = physical Fourier transform of orthonormal even basis; G=E.T*E; both-zero-side candidate=2G','source_sha256':{str(source.relative_to(BASE)):hashlib.sha256(source.read_bytes()).hexdigest(),'zeros.csv':hashlib.sha256((OUT/'zeros.csv').read_bytes()).hexdigest()},'E':E,'G':G,'A':A,'V':V,'A_eigenvalues':ae,'G_eigenvalues':list(g),'2G_eigenvalues':[2*x for x in g],'U':U,'A_minus_2G':residual,'A_minus_2G_eigenvalues':list(re),'A_minus_2G_operator_norm':max(abs(x) for x in re),'A_minus_G_operator_norm':max(abs(x) for x in single),'A_G_eigenvector_overlap_squared':overlap,'A_in_G_basis':U.T*A*U,'resolved_G_indices':resolved,'G_resolution_tolerance':tol,'W':W,'W_orthogonality_residual':mp.norm(W.T*W-mp.eye(len(resolved))),'G_eigen_residual':mp.norm(G*U-U*mp.diag(g)),'G_eigenvector_orthogonality_residual':mp.norm(U.T*U-mp.eye(d)),'prefixes':prefixrows,'elapsed':time.monotonic()-start}
 (OUT/f'cell_m{m}.json').write_text(json.dumps(serial(out),indent=2)+'\n');print('COMPLETE',m,out['elapsed'],flush=True)

def aggregate():
 rows=[];conv=[]
 for m in (16,24):
  d=json.loads((OUT/f'cell_m{m}.json').read_text())
  for p in d['prefixes']:
   r={k:v for k,v in p.items() if not isinstance(v,list)};r={'m':m,**r};conv.append(r)
   for i,v in enumerate(p['g_eigenvalues']):rows.append({'m':m,'q':p['q'],'height':p['height'],'index':i,'G_eigenvalue':v,'2G_eigenvalue':mp.nstr(2*mp.mpf(v),180),'A_eigenvalue':d['A_eigenvalues'][i],'resolution':p['resolution_classes'][i],'relative_G_change_from_full':p['relative_eigenvalue_difference_from_full'][i]})
 for name,data in [('spectra.csv',rows),('convergence.csv',conv)]:
  with (OUT/name).open('w',newline='') as f:
   w=csv.DictWriter(f,fieldnames=data[0]);w.writeheader();w.writerows(data)
if __name__=='__main__':
 mp.mp.dps=180
 if sys.argv[1]=='aggregate':aggregate()
 else:compute(int(sys.argv[1]))
