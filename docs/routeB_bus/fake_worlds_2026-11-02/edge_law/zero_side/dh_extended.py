"""Reevaluate unchanged DH vectors on extended310 census, no eigensolve."""
from pathlib import Path
import csv,json,hashlib
import mpmath as mp
mp.mp.dps=120
OUT=Path(__file__).resolve().parent;DH=OUT.parent/'dh';ZPATH=DH/'dh_zeros_extended.json';zd=json.loads(ZPATH.read_text());fmt=lambda x:mp.nstr(x,90)
rows=[];quartets=[];nodes=[];sources=[];missing=[]
for m in (160,200,240):
 for mode in ('matched','native'):
  p=DH/f'cell_m{m}_{mode}_dps120_gl192.json'
  if not p.exists():missing.append(p.name);continue
  d=json.loads(p.read_text());f=[mp.mpf(x) for x in d['physical_modal_coefficients']];norm=mp.sqrt(mp.fsum(x*x for x in f));f=[x/norm for x in f];L=mp.log(m);b=L/2;om=[2*mp.pi*n/L for n in range(m+1)];ds=[mp.mpf(1)]+[mp.sqrt(2)]*m;T=mp.mpf(d['T']);case=f'dh_m{m}_{mode}';ray=mp.mpf(d['source_Rayleigh'])
  def F(z):return 2*mp.sin(b*z)/mp.sqrt(L)*mp.fsum(ds[n]*f[n]*z/(z*z-om[n]**2) for n in range(m+1))
  line_lo=line_hi=quart_lo=quart_hi=G=M_im=mp.mpf(0);vals=[]
  for x in zd['critical_line_zeros']:
   g=mp.mpf(x['gamma']);v=F(g);term=2*v*v;G+=v*v
   if g<=T:line_lo+=term
   else:line_hi+=term
   nodes.append(dict(case=case,kind='line',gamma=fmt(g),delta='0',below_T=g<=T,ReF=fmt(v),ImF='0',full_orbit=fmt(term)))
  for x in zd['off_line_pairs']:
   g=mp.mpf(x['gamma']);delta=mp.mpf(x['sigma_right'])-mp.mpf('.5');v=F(mp.mpc(g,delta));a=mp.re(v);bb=mp.im(v);term=4*(a*a-bb*bb);ordinary=4*(a*a+bb*bb);correction=-8*bb*bb;G+=2*abs(v)**2;M_im+=2*bb*bb
   if g<=T:quart_lo+=term
   else:quart_hi+=term
   vals.append((g,term));quartets.append(dict(case=case,m=m,mode=mode,q=d['q'],T=fmt(T),gamma=fmt(g),delta=fmt(delta),listed_multiplicity=1,below_T=g<=T,ReF=fmt(a),ImF=fmt(bb),positive_square_term=fmt(4*a*a),negative_square_term=fmt(-4*bb*bb),Weil_quartet=fmt(term),ordinary_2G_quartet=fmt(ordinary),metric_correction_minus8ImSquared=fmt(correction)))
  total=line_lo+line_hi+quart_lo+quart_hi;err=total-(2*G-4*M_im);assert abs(err)<mp.mpf('1e-95')
  smallest=min(vals,key=lambda x:x[1]);new=vals[-1];first=min(vals,key=lambda x:x[0]);prediction=smallest[0]==first[0]
  rows.append(dict(case=case,m=m,mode=mode,q=d['q'],T=fmt(T),census_height=310,critical_line_nodes=len(zd['critical_line_zeros']),listed_quartets=len(zd['off_line_pairs']),source_Rayleigh=fmt(ray),line_below_T=fmt(line_lo),quartet_below_T=fmt(quart_lo),Weil_below_T=fmt(line_lo+quart_lo),line_T_to_310=fmt(line_hi),quartet_T_to_310=fmt(quart_hi),Weil_T_to_310=fmt(line_hi+quart_hi),Weil_through_310=fmt(total),unpaid_source_minus_prefix=fmt(ray-total),ordinary_positive_G=fmt(G),imag_square_mass=fmt(M_im),metric_correction_minus4M_im=fmt(-4*M_im),metric_identity_error=fmt(err),new_pair_height=fmt(new[0]),new_pair_contribution=fmt(new[1]),new_pair_below_T=new[0]<=T,most_negative_pair_height=fmt(smallest[0]),first_pair_most_negative_prediction=prediction,producer_original_census_height=d.get('census_height_bound'),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
  sources.append(dict(file=p.name,sha256=hashlib.sha256(p.read_bytes()).hexdigest()));print(case,'T',mp.nstr(T,8),'prefix',mp.nstr(total,12),'newpair',mp.nstr(new[1],12),'firstmostnegative',prediction,flush=True)
for name,rr in [('dh_extended.csv',rows),('dh_extended_quartets.csv',quartets)]:
 with (OUT/name).open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=list(rr[0]));w.writeheader();w.writerows(rr)
(OUT/'dh_extended_provenance.json').write_text(json.dumps(dict(status='NUMERICAL_PREFIX_NOT_CERTIFIED',dps=120,missing_cells=missing,zero_census_sha256=hashlib.sha256(ZPATH.read_bytes()).hexdigest(),source_files=sources,code_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()),indent=2)+'\n')
