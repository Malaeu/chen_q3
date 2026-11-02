"""EDGE_LAW_v1 zeta complements: full literal matrix and endpoint diagnostic."""
from pathlib import Path
import sys,json,csv,time,hashlib,gzip
import mpmath as mp
P=Path(__file__).resolve().parent;FAKE=P.parents[1];BUS=FAKE.parent
sys.path.insert(0,str(FAKE/'ledger_diff'));from matched import build_zeta
sys.path.insert(0,str(BUS/'capacity_matrix_2026-11-02'));from capacity import Erow
ZPATH=BUS/'capacity_matrix_2026-11-02/zeros.csv'

def serial(v,dps):
 if isinstance(v,mp.matrix):return [[mp.nstr(v[i,j],dps) for j in range(v.cols)] for i in range(v.rows)]
 if isinstance(v,(list,tuple)):return [serial(x,dps) for x in v]
 if isinstance(v,dict):return {k:serial(x,dps) for k,x in v.items()}
 if isinstance(v,mp.mpf):return mp.nstr(v,dps)
 return v

def run(m,dps=120,order=192):
 start=time.monotonic();mp.mp.dps=dps;L=mp.log(m);Omega=2*mp.pi*m/L;T=mp.mpf('1.1')*Omega;zeros=[mp.mpf(r['gamma']) for r in csv.DictReader(ZPATH.open())];selected=[g for g in zeros if g<T];q=len(selected);d=m+1
 builder_hash=hashlib.sha256((FAKE/'ledger_diff/matched.py').read_bytes()+(BUS/'phase_space_V/v_forms.py').read_bytes()).hexdigest()[:16]
 acache=Path('/tmp')/f'edge_zeta_A_m{m}_dps{dps}_gl{order}_{builder_hash}.json.gz'
 if acache.exists():
  with gzip.open(acache,'rt') as z:A=mp.matrix(json.load(z))
 else:
  A=build_zeta(m,dps,order)
  with gzip.open(acache,'wt') as z:json.dump(serial(A,dps),z)
 print('MATRIX',m,round(time.monotonic()-start,2),flush=True)
 E=mp.matrix([Erow(g,m) for g in selected]);scales=[mp.norm(E[i,:]) for i in range(q)];F=mp.matrix([[E[i,j]/scales[i] for j in range(d)] for i in range(q)])
 U,R=mp.qr(F.T,mode='skinny',edps=20);print('QR',m,q,round(time.monotonic()-start,2),flush=True)
 # Triangular inverse supplies a conservative finite-dimensional conditioning bound.
 Ri=mp.zeros(q)
 for j in range(q):
  Ri[j,j]=1/R[j,j]
  for i in range(j-1,-1,-1):Ri[i,j]=-mp.fsum(R[i,k]*Ri[k,j] for k in range(i+1,j+1))/R[i,i]
 with mp.workdps(dps+30):
  qrres=mp.norm(F.T-U*R);orth=mp.norm(U.T*U-mp.eye(q))
 sigma_lower=1/mp.norm(Ri)
 C=U.T*(A*U);ev,Y=mp.eigsy(C);y=Y[:,0];f=U*y;f/=mp.norm(f);pivot=max(range(d),key=lambda i:abs(f[i]));f*=1 if f[pivot]>=0 else -1
 checkpoint=Path('/tmp')/f'edge_zeta_raw_eigenpair_m{m}_dps{dps}_gl{order}.json'
 checkpoint.write_text(json.dumps(serial(dict(m=m,dps=dps,order=order,q=q,L=L,T=T,complement_minimum=ev[0],complement_gap=ev[1]-ev[0],complement_f=list(f),complement_y=list(y)),dps))+'\n')
 lam=mp.fdot(f,A*f);endpoint=mp.fsum(f[n]*(1 if n==0 else mp.sqrt(2)) for n in range(d))/mp.sqrt(L);endpoint_literal=mp.fsum(f[n]*(1 if n==0 else mp.sqrt(2))*(-1)**n*mp.cos(mp.pi*n) for n in range(d))/mp.sqrt(L);lawscale=endpoint**2*mp.log(T)/(mp.pi*T);ratio=lam/lawscale
 result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',world='zeta',m=m,N=m,dps=dps,order=order,q=q,rank=q,L=L,Omega=Omega,T=T,kappa=mp.mpf('1.1'),cutoff_mode='native_kappa1p1',last_included_zero=selected[-1],first_excluded_zero=zeros[q],complement_minimum=ev[0],complement_rayleigh=lam,complement_gap=ev[1]-ev[0],complement_f=list(f),complement_norm=mp.norm(f),endpoint_f_b=endpoint,endpoint_squared=endpoint**2,endpoint_literal_difference=endpoint-endpoint_literal,edge_scale=lawscale,R=ratio,predicted_interval=[3,5],finite_prediction_pass=bool(3<=ratio<=5),QR_reconstruction_residual=qrres,U_orthogonality_residual=orth,scaled_E_sigma_lower_bound=sigma_lower,scaled_E_condition_upper_bound=mp.norm(R)*mp.norm(Ri),rank_margin_lower_bound_over_QR_residual=sigma_lower/qrres if qrres else None,compressed_eigenpair_residual=mp.norm(C*y-ev[0]*y),Rayleigh_minus_eigenvalue=lam-ev[0],basis='e0=1/sqrtL; en=sqrt(2/L)*(-1)^n*cos(2pi*n*x/L), zero outside; endpoint=sum dn*fn/sqrtL',source_hashes={str(p.relative_to(BUS)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [FAKE/'ledger_diff/matched.py',BUS/'capacity_matrix_2026-11-02/capacity.py',ZPATH]},prediction_sha256=hashlib.sha256((P/'PREDICTIONS.md').read_bytes()).hexdigest(),seconds=time.monotonic()-start)
 name=f'cell_m{m}_dps{dps}_gl{order}';local=Path('/tmp')/('edge_law_zeta_'+name+'.json.gz')
 with gzip.open(local,'wt') as z:json.dump(serial(dict(A=A,U=U,R=R,E=E,C=C),dps),z)
 result['dense_cache_local']=str(local);(P/(name+'.json')).write_text(json.dumps(serial(result,dps),indent=2)+'\n');print('DONE',m,'lambda',mp.nstr(lam,16),'R',mp.nstr(ratio,16),'seconds',time.monotonic()-start,flush=True)
if __name__=='__main__':run(*map(int,sys.argv[1:]))
