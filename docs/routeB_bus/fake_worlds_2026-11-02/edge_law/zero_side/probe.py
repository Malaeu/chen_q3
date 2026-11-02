"""Finite known-zero sums and exact endpoint rational remainder; no RH input."""
from pathlib import Path
import csv,json,hashlib
import mpmath as mp
mp.mp.dps=120
OUT=Path(__file__).resolve().parent;ROOT=OUT.parents[1];BUS=ROOT.parent
zerosfile=BUS/'capacity_matrix_2026-11-02/zeros.csv'
zg=[mp.mpf(r['gamma']) for r in csv.DictReader(zerosfile.open()) if mp.mpf(r['gamma'])<=400]
dhz=json.loads((ROOT/'dh_zeros.json').read_text());rows=[];nodes=[];sources=[]
cases=[]
for p in sorted((ROOT/'ledger_diff/ledger_cells').glob('*.json')):
 d=json.loads(p.read_text());s=d['summary'];cases.append((p,d['unit_physical_modal_vector'],s['world'],int(s['m']),int(s['q']),s['cutoff_T'],s['same_vector_Rayleigh'],s['cutoff_mode']))
# New stable publication cells are included automatically once present.
for p in sorted((ROOT/'edge_law/zeta').glob('cell_m*_dps120_gl192.json')):
 d=json.loads(p.read_text());cases.append((p,d['complement_f'],'zeta',int(d['m']),int(d['q']),d['T'],d['complement_rayleigh'],d['cutoff_mode']))
fmt=lambda x:mp.nstr(x,70)
for path,coeff,world,m,q,T,ray,mode in cases:
 f=[mp.mpf(x) for x in coeff];norm=mp.sqrt(mp.fsum(x*x for x in f));f=[x/norm for x in f];L=mp.log(m);b=L/2;ds=[mp.mpf(1)]+[mp.sqrt(2)]*m;om=[2*mp.pi*n/L for n in range(m+1)];Omega=om[-1];T=mp.mpf(T);fb=mp.fsum(ds[n]*f[n] for n in range(m+1))/mp.sqrt(L);C=mp.fsum(abs(ds[n]*f[n])*om[n]**2 for n in range(m+1))/mp.sqrt(L)
 def F(z):return 2*mp.sin(b*z)/mp.sqrt(L)*mp.fsum(ds[n]*f[n]*z/(z*z-om[n]**2) for n in range(m+1))
 def stableF(z):return mp.fsum(ds[n]*(-1)**n*f[n]/mp.sqrt(L)*b*(mp.sinc((z-om[n])*b)+mp.sinc((z+om[n])*b)) for n in range(m+1))
 zz=[(g,mp.mpf(0)) for g in zg] if world=='zeta' else [(mp.mpf(x['gamma']),mp.mpf(x['sigma'])-mp.mpf('.5')) for x in dhz['upper_half_plane_zeros']]
 sumlo=sumhi=G=M_im=mp.mpf(0);edgehi=mp.mpf(0);crosshi=mp.mpf(0);remhi=mp.mpf(0);boundhi=mp.mpf(0);maxidentity=maxviolation=mp.mpf(0)
 for g,delta in zz:
  z=mp.mpc(g,delta);v=F(z);actual=2*mp.re(v*v);gg=abs(v)**2;nn=mp.im(v)**2;G+=gg;M_im+=nn
  if g<=T:sumlo+=actual
  else:sumhi+=actual
  if delta==0 and g>T and g>Omega:
   edge=2*fb*mp.sin(b*g)/g;rembound=2*abs(mp.sin(b*g))*C/(g*(g*g-Omega*Omega));edgehi+=2*edge**2;crosshi+=4*edge*mp.re(v-edge);remhi+=2*abs(v-edge)**2;boundhi+=2*(2*abs(edge)*rembound+rembound**2);maxviolation=max(maxviolation,abs(v-edge)-rembound)
  if len(nodes)%17==0:maxidentity=max(maxidentity,abs(v-stableF(z)))
  nodes.append(dict(case=f'{world}_m{m}_q{q}_{mode}',gamma=fmt(g),delta=fmt(delta),below_cutoff=g<=T,ReF=fmt(mp.re(v)),ImF=fmt(mp.im(v)),Weil_pair=fmt(actual),ordinary_positive_Gram=fmt(gg),imag_square_mass=fmt(nn)))
 if world=='zeta':assert abs(sumhi-edgehi-crosshi-remhi)<mp.mpf('1e-90')
 total=sumlo+sumhi;identity=total-(2*G-4*M_im)
 assert abs(identity)<mp.mpf('1e-90') and maxidentity<mp.mpf('1e-90') and maxviolation<mp.mpf('1e-90')
 rows.append(dict(world=world,m=m,q=q,mode=mode,T=fmt(T),Omega=fmt(Omega),X=400 if world=='zeta' else dhz['height_bound'],positive_nodes=len(zz),endpoint=fmt(fb),endpoint_squared=fmt(fb*fb),C_remainder=fmt(C),source_Rayleigh=ray,Weil_below_T=fmt(sumlo),Weil_T_to_X=fmt(sumhi),Weil_through_X=fmt(total),positive_Gram_through_X=fmt(G),imag_square_mass=fmt(M_im),metric_correction_minus4imag_square_mass=fmt(-4*M_im),Gram_identity_error=fmt(identity),source_minus_partial=fmt(mp.mpf(ray)-total),endpoint_only_T_to_X=fmt(edgehi) if world=='zeta' else '',edge_remainder_cross_T_to_X=fmt(crosshi) if world=='zeta' else '',remainder_square_T_to_X=fmt(remhi) if world=='zeta' else '',square_expansion_error=fmt(sumhi-edgehi-crosshi-remhi) if world=='zeta' else '',endpoint_error_bound_T_to_X=fmt(boundhi) if world=='zeta' else '',far_tail_averaged_endpoint_heuristic=fmt(2*fb*fb/mp.pi*(mp.log(mp.mpf(400)/(2*mp.pi))+1)/400) if world=='zeta' else '',modal_identity_error=fmt(maxidentity),remainder_bound_max_violation=fmt(maxviolation)))
 sources.append(dict(path=str(path),sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
for name,data in [('zero_sums.csv',rows),('node_values.csv',nodes)]:
 with (OUT/name).open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=list(data[0]));w.writeheader();w.writerows(data)
quartets=[]
for node in nodes:
 if mp.mpf(node['delta'])<=0:continue
 re=mp.mpf(node['ReF']);im=mp.mpf(node['ImF'])
 quartets.append(dict(case=node['case'],gamma=node['gamma'],delta=node['delta'],listed_multiplicity=1,below_cutoff=node['below_cutoff'],ReF=node['ReF'],ImF=node['ImF'],Weil_quartet=fmt(4*(re*re-im*im)),ordinary_2G_quartet=fmt(4*(re*re+im*im)),metric_correction_minus8ImSquared=fmt(-8*im*im)))
with (OUT/'quartets.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=list(quartets[0]));w.writeheader();w.writerows(quartets)
(OUT/'provenance.json').write_text(json.dumps(dict(status='DIAGNOSTIC_KNOWN_ZERO_PREFIX_NOT_GLOBAL_RH',dps=120,zeta_zero_sha256=hashlib.sha256(zerosfile.read_bytes()).hexdigest(),dh_zero_sha256=hashlib.sha256((ROOT/'dh_zeros.json').read_bytes()).hexdigest(),sources=sources),indent=2)+'\n')
for r in rows:print(r['world'],r['m'],r['q'],r['mode'],'lo',mp.nstr(mp.mpf(r['Weil_below_T']),7),'hi',mp.nstr(mp.mpf(r['Weil_T_to_X']),7),'diff',mp.nstr(mp.mpf(r['source_minus_partial']),7),'edgehi',mp.nstr(mp.mpf(r['endpoint_only_T_to_X'] or 0),7))
