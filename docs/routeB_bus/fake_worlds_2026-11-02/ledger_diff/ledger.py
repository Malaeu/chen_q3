"""Signed complement-vector ledger with independent segmented Abel integration.
DIAGNOSTIC_NEVER_A_PROOF. All terms use the same unit physical modal vector.
"""
from pathlib import Path
import sys,json,csv,hashlib,time
import mpmath as mp
P=Path(__file__).resolve().parent;OUT=P/'ledger_cells';OUT.mkdir(exist_ok=True)
sys.path.insert(0,str(P.parent));from dh_matrix import coeffs
sys.path.insert(0,str(P.parents[1]/'phase_space_V'));from v_forms import mangoldt

def prime_sector(n):
 for p in range(2,n+1):
  if n%p==0:
   q=n;k=0
   while q%p==0:q//=p;k+=1
   if q!=1:return 'nonprimepower'
   return 'prime' if k==1 else ('square' if k==2 else 'higherpower')

def exp_mom(z,a,b):
 ea=mp.exp(z*a);eb=mp.exp(z*b)
 return (eb-ea)/z,(eb*(z*b-1)-ea*(z*a-1))/(z*z)

def run(world,m,q,native=False):
 start=time.monotonic();mp.mp.dps=140;suffix='_native' if native else '';source=P/'matched_cells'/f'{world}_m{m}_q{q}{suffix}.json';data=json.loads(source.read_text());f=mp.matrix(data['complement_f']);f/=mp.norm(f);A=mp.matrix(data['A']);L=mp.log(m);omega=2*mp.pi/L;sqrtL=mp.sqrt(L);ds=[mp.mpf(1)]+[mp.sqrt(2)]*m
 fmt=lambda x:mp.nstr(mp.re(x),125)
 # Independent physical exponential product coefficients for Q and J=2 integral f f'_int.
 modes=list(range(-m,m+1));a={n:f[abs(n)]*ds[abs(n)]*(-1 if n%2 else 1)/(sqrtL*(1 if n==0 else 2)) for n in modes}
 Q0={n:mp.mpc(0) for n in modes};Q1=Q0.copy();J0=Q0.copy();J1=Q0.copy()
 for k in modes:
  for l in modes:
   base=2*a[k]*a[l]
   if k+l==0:
    Q0[l]+=base*L;Q1[l]-=base;J0[l]+=base*mp.j*omega*l*L;J1[l]-=base*mp.j*omega*l
   else:
    c=base*(-1 if (k+l)%2 else 1)/(mp.j*omega*(k+l));v=c*mp.j*omega*l
    Q0[-k]+=c;Q0[l]-=c;J0[-k]+=v;J0[l]-=v
 fb=mp.fsum(f[n]*ds[n] for n in range(m+1))/sqrtL
 B0={n:2*fb*f[abs(n)]*ds[abs(n)]/(sqrtL*(1 if n==0 else 2)) for n in modes}
 derivative_identity=max(max(abs(J0[n]-(mp.j*omega*n*Q0[n]+Q1[n])-B0[n]),abs(J1[n]-mp.j*omega*n*Q1[n])) for n in modes)
 # Separate coefficients obtained directly by contracting q_even, not the physical product above.
 sincoef=[mp.mpf(0)]*(m+1)
 for i in range(1,m+1):sincoef[i]-=f[i]**2/(mp.pi*i)
 for i in range(m+1):
  for k in range(i+1,m+1):
   v=2*f[i]*f[k]*ds[i]*ds[k]/(mp.pi*(i*i-k*k));sincoef[k]+=v*k;sincoef[i]-=v*i
 def correlation(s):
  if s>=L:return mp.mpf(0)
  co=mp.cos(omega*s);si=mp.sin(omega*s);cn=mp.mpf(1);sn=mp.mpf(0);total=mp.mpf(0)
  for n in range(m+1):
   total+=2*f[n]**2*(1-s/L)*cn+sincoef[n]*sn;cn,sn=cn*co-sn*si,sn*co+cn*si
  return total
 def series(Q0,Q1,s):return mp.re(mp.fsum((Q0[n]+s*Q1[n])*mp.exp(mp.j*omega*n*s) for n in modes))
 correlation_check=max(abs(correlation(L*r)-series(Q0,Q1,L*r)) for r in [mp.mpf('.123'),mp.mpf('.456'),mp.mpf('.789')])
 b=[mp.mpf(0)]*(m+1)
 if world=='dh':_,b=coeffs(m)
 else:
  for n in range(2,m+1):b[n]=mangoldt(n)
 groups={sector+'_'+sign:mp.mpf(0) for sector in ['prime','square','higherpower','nonprimepower'] for sign in ['b_positive','b_negative']};atoms=[]
 for n in range(2,m+1):
  Qval=mp.mpf(0) if n==m else correlation(mp.log(n));raw=b[n]/mp.sqrt(n)*Qval;sector=prime_sector(n);sign='b_positive' if b[n]>0 else ('b_negative' if b[n]<0 else 'b_zero')
  if b[n]:groups[sector+'_'+sign]+=raw
  atoms.append(dict(n=n,sector=sector,coefficient_sign=sign,b_n=fmt(b[n]),Q_log_n=fmt(Qval),raw_P=fmt(raw),signed_ledger_minus_P=fmt(-raw),endpoint_atom=n==m))
 Ptotal=mp.fsum(groups.values())
 # Exact exponential moments, independently segmented at EVERY integer logarithm.
 totals=[mp.mpc(0)]*3;Psi=mp.mpf(0)
 for j in range(1,m):
  if j>=2:Psi+=b[j]
  lo=mp.log(j);hi=mp.log(j+1);weight=Psi+(1 if world=='zeta' else 0)
  for n in modes:
   M0,M1=exp_mom(-mp.mpf('.5')+mp.j*omega*n,lo,hi);M0*=weight;M1*=weight
   if world=='zeta':
    C0,C1=exp_mom(mp.mpf('.5')+mp.j*omega*n,lo,hi);M0-=C0;M1-=C1
   totals[0]+=Q0[n]*M0+Q1[n]*M1;totals[1]+=J0[n]*M0+J1[n]*M1;totals[2]+=B0[n]*M0
 T=mp.re(totals[0])/2;bulk=-mp.re(totals[1]);boundary=mp.re(totals[2]);interior=T+bulk
 def integrated_Q(alpha):return mp.re(mp.fsum(Q0[n]*exp_mom(alpha+mp.j*omega*n,0,L)[0]+Q1[n]*exp_mom(alpha+mp.j*omega*n,0,L)[1] for n in modes))
 continuum=integrated_Q(mp.mpf('.5'));Rminus=integrated_Q(-mp.mpf('.5'))
 def ref_integral(C0,C1):
  out=mp.mpc(0)
  for n in modes:
   a0,a1=exp_mom(mp.mpf('.5')+mp.j*omega*n,0,L);b0,b1=exp_mom(-mp.mpf('.5')+mp.j*omega*n,0,L);out+=C0[n]*(a0-b0)+C1[n]*(a1-b1)
  return mp.re(out)
 if world=='dh':
  reference_T=T-(continuum-Rminus)/2;reference_bulk=bulk+ref_integral(J0,J1);reference_B=boundary-ref_integral(B0,{n:mp.mpc(0) for n in modes})
 else:reference_T,reference_bulk,reference_B=T,bulk,boundary
 # Independent positive arch quadrature, including the full infinite tail.
 gn,gw=mp.gauss_quadrature(160,'legendre');nodes=[(L*(panel+(x+1)/2)/8,L*w/16) for panel in range(8) for x,w in zip(gn,gw)]
 def tail(alpha):
  out=mp.mpf(0);k=0
  while True:
   term=mp.exp(-(alpha+2*k)*L)/(alpha+2*k);out+=term
   if abs(term)<mp.mpf('1e-145'):return out
   k+=1
 alphas=[mp.mpf('.5'),mp.mpf('2.5')] if world=='zeta' else [mp.mpf('1.5')];Hs=[]
 qvals=[correlation(s) for s,w in nodes]
 for alpha in alphas:Hs.append(mp.fsum(w*mp.exp(-alpha*s)/(-mp.expm1(-2*s))*(2-Qval) for (s,w),Qval in zip(nodes,qvals))+2*tail(alpha))
 H=Hs[0];cstar=mp.euler+mp.log(8*mp.pi)+mp.pi/2;c=-cstar if world=='zeta' else -mp.euler-mp.log(8*mp.pi/5)+mp.pi/2
 polevec=[4*mp.sqrt(2)*ds[n]*L**mp.mpf('1.5')*mp.sinh(L/4)/(L*L+16*mp.pi**2*n*n) for n in range(m+1)]
 pole=mp.fdot(f,polevec)**2 if world=='zeta' else mp.mpf(0);rayleigh=mp.fdot(f,A*f);direct=H+c+pole-Ptotal;S=Ptotal-(continuum if world=='zeta' else 0)
 cutoff_mode=data.get('cutoff_mode') or ('native_kappa1p1' if native or (world=='zeta' and q=={55:27,80:41,120:64}[m]) else ('density_matched_lower' if m==120 and q==63 else ('density_matched_upper' if m==120 and q==65 else 'density_matched')))
 summary=dict(world=world,m=m,q=q,cutoff_mode=cutoff_mode,cutoff_T=data.get('T'),scalar_H_sign='positive_coefficient',scalar_constant_sign='negative_coefficient',scalar_pole_sign='positive_coefficient' if world=='zeta' else 'absent_exact_zero',rank=data.get('rank',q),working_dps=140,arch_GL_order=160,vector_norm_squared=fmt(mp.fdot(f,f)),complement_minimum=data['complement_minimum'],same_vector_Rayleigh=fmt(rayleigh),H_original=fmt(H),constant_original=fmt(c),pole=fmt(pole),raw_P_total=fmt(Ptotal),signed_minus_P_total=fmt(-Ptotal),direct_ledger_sum=fmt(direct),direct_ledger_minus_Rayleigh=fmt(direct-rayleigh),continuum_I_L=fmt(continuum),canonical_continuum_subtracted=fmt(continuum if world=='zeta' else 0),reference_Abel_convention='SOURCE_COMPENSATED' if world=='zeta' else 'ARBITRARY_REFERENCE_NO_POLE_CANCELLATION',reference_T=fmt(reference_T),reference_derivative_bulk=fmt(reference_bulk),reference_B=fmt(reference_B),reference_full_interior=fmt(reference_T+reference_bulk),reference_Abel_closure_error=fmt(Ptotal-continuum-reference_T-reference_bulk-reference_B),reference_ledger_sum=fmt(H+c+pole-Ptotal) if world=='zeta' else fmt(H+c-continuum-reference_T-reference_bulk-reference_B),raw_Abel_target=fmt(S),half_correlation_T=fmt(T),derivative_bulk=fmt(bulk),boundary_B=fmt(boundary),full_interior_T_plus_bulk=fmt(interior),Abel_sum=fmt(interior+boundary),Abel_closure_error=fmt(S-interior-boundary),endpoint_f_b=fmt(fb),derivative_identity_coefficient_error=fmt(derivative_identity),independent_correlation_error=fmt(correlation_check),segment_count=m-1,endpoint_atom_zero=True)
 for key,v in groups.items():summary['raw_P_'+key]=fmt(v);summary['signed_minus_P_'+key]=fmt(-v)
 if world=='zeta':
  Hp=Hs[1];compc=4-cstar;high=groups['higherpower_b_positive']+groups['higherpower_b_negative'];S12=S-high
  summary.update(H_plus=fmt(Hp),constant_compensated=fmt(compc),R_minus=fmt(Rminus),compensated_ledger_sum=fmt(Hp+compc-S),compensated_minus_Rayleigh=fmt(Hp+compc-S-rayleigh),arch_shift_identity_error=fmt(H-Hp-4+Rminus),pole_continuum_identity_error=fmt(pole-continuum-Rminus),S12=fmt(S12),joint_S12_minus_Hplus=fmt(S12-Hp))
 else:
  for key in ['H_plus','constant_compensated','R_minus','compensated_ledger_sum','compensated_minus_Rayleigh','arch_shift_identity_error','pole_continuum_identity_error','S12','joint_S12_minus_Hplus']:summary[key]=None
 result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',summary=summary,groups={k:dict(raw_P=fmt(v),signed_ledger_minus_P=fmt(-v)) for k,v in groups.items()},atoms=atoms,unit_physical_modal_vector=[fmt(x) for x in f],source_file=str(source.relative_to(P)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),code_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),conventions_sha256=hashlib.sha256((P/'SOURCE_CONVENTIONS.md').read_bytes()).hexdigest(),seconds=time.monotonic()-start)
 (OUT/f'{world}_m{m}_q{q}{suffix}.json').write_text(json.dumps(result,indent=2)+'\n');print(world,m,q,'lambda',fmt(rayleigh)[:20],'direct error',mp.nstr(direct-rayleigh,8),'Abel error',mp.nstr(S-interior-boundary,8),'seconds',result['seconds'],flush=True)

def aggregate():
 rows=[]
 for p in sorted(OUT.glob('*.json')):
  d=json.loads(p.read_text());d['code_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest();d['serialization_significant_digits']=125;d['closure_residual_scope']='Computed internally at140dps before125-digit serialization';p.write_text(json.dumps(d,indent=2)+'\n');rows.append(d['summary'])
 with (P/'ledger.csv').open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
if __name__=='__main__':
 if sys.argv[1]=='aggregate':aggregate()
 else:run(sys.argv[1],int(sys.argv[2]),int(sys.argv[3]),len(sys.argv)>4 and sys.argv[4]=='native')
