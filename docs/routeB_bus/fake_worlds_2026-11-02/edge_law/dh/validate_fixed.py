"""Independent scalar DH Rayleigh quadrature on one saved physical modal vector."""
from pathlib import Path
import sys,json,time,hashlib
import mpmath as mp
P=Path(__file__).resolve().parent;FAKE=P.parents[1]
sys.path.insert(0,str(P));sys.path.insert(0,str(FAKE))
from extend_zeros import register
from dh_matrix import coeffs

def run(m,mode):
 register(f'Fixed-vector DH m{m} {mode},160dps GL256','Independently assembled scalar correlation/source should agree with saved120dps GL192 matrix Rayleigh quotient well below displayed digits. Endpoint evaluated on the same normalized fixed vector.','A substantial discrepancy blocks precision-validation status; this check does not establish census completeness or a global eigenvalue enclosure.')
 start=time.monotonic();mp.mp.dps=160;path=P/f'cell_m{m}_{mode}_dps120_gl192.json';d=json.loads(path.read_text());f=list(map(mp.mpf,d['physical_modal_coefficients']));L=mp.log(m);norm=mp.fsum(c*c for c in f);ds=[mp.mpf(1)]+[mp.sqrt(2)]*m
 aa=[c*c for c in f];bb=[mp.mpf(0)]*(m+1)
 for n in range(1,m+1):bb[n]=-aa[n]/(mp.pi*n)+2*ds[n]*f[n]*n/mp.pi*mp.fsum(ds[j]*f[j]/(j*j-n*n) for j in range(m+1) if j!=n)
 def Q(s):
  co=mp.cos(2*mp.pi*s/L);si=mp.sin(2*mp.pi*s/L);cn=mp.mpf(1);sn=mp.mpf(0);c=mp.mpf(0);v=mp.mpf(0)
  for n in range(m+1):
   c+=aa[n]*cn;v+=bb[n]*sn;cn,sn=cn*co-sn*si,sn*co+cn*si
  return 2*(1-s/L)*c+v
 gn,gw=mp.gauss_quadrature(256,'legendre');arch=mp.mpf(0)
 for p in range(8):
  for z,w in zip(gn,gw):
   s=L*(mp.mpf(p)+(z+1)/2)/8;arch+=L*w/16*mp.exp(-mp.mpf('1.5')*s)/(-mp.expm1(-2*s))*(2*norm-Q(s))
 tail=mp.atanh(mp.exp(-L/2))-mp.atan(mp.exp(-L/2));arch+=2*norm*tail
 _,b=coeffs(m);prime=mp.fsum(b[n]/mp.sqrt(n)*Q(mp.log(n)) for n in range(2,m));constant=mp.log(5/mp.pi)+mp.digamma(mp.mpf('.75'));ray=(arch+constant*norm-prime)/norm
 A=mp.matrix(json.loads((P/f'source_m{m}_dps120_gl192.json').read_text())['A']);v=mp.matrix(f);low=mp.fdot(v,A*v)/norm
 edge=mp.fsum(ds[n]*f[n] for n in range(m+1))/mp.sqrt(L*norm);T=mp.mpf(d['T']);ratio=ray/(edge*edge*mp.log(T)/(mp.pi*T));fmt=lambda x:mp.nstr(x,140)
 out={'status':'DIAGNOSTIC_PRECISION_CHECK_NOT_INTERVAL_CERTIFIED','m':m,'mode':mode,'validation_dps':160,'validation_order':256,'source_dps':120,'source_order':192,'fixed_vector_norm_squared':fmt(norm),'scalar_Q_zero_minus_2norm':fmt(Q(0)-2*norm),'scalar_Q_L':fmt(Q(L)),'arch':fmt(arch/norm),'signed_constant':fmt(constant),'raw_arithmetic':fmt(prime/norm),'scalar_Rayleigh_high':fmt(ray),'fixed_vector_matrix_Rayleigh_low':fmt(low),'absolute_Rayleigh_difference':fmt(abs(ray-low)),'relative_Rayleigh_difference':fmt(abs(ray-low)/abs(ray)),'endpoint_squared_high':fmt(edge*edge),'R_edge_high':fmt(ratio),'R_edge_saved':d['R_edge'],'relative_R_edge_change':fmt(abs(ratio-mp.mpf(d['R_edge']))/abs(ratio)),'source_cell_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'seconds':time.monotonic()-start}
 (P/f'validation_m{m}_{mode}.json').write_text(json.dumps(out,indent=2)+'\n');print('VALIDATED',m,mode,out['relative_Rayleigh_difference'],flush=True)
if __name__=='__main__':run(int(sys.argv[1]),sys.argv[2])
