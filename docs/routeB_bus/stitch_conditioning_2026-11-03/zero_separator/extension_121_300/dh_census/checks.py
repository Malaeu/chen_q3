"""Independent spot checks and numerical multiplicity diagnostics; no certification."""
from extend import *
import csv

def main():
 d=json.loads((P/'dh_zeros_600.json').read_text());old=json.loads(INPUT.read_text());mp.mp.dps=100
 errors=[]
 for a,b in zip(old['critical_line_zeros'],d['critical_line_zeros']):errors.append(abs(mp.mpf(a['gamma'])-mp.mpf(b['gamma'])))
 off=[]
 for r in d['off_line_pairs']:
  seed=mp.mpc(r['sigma_right'],r['gamma']);mp.mp.dps=120;z=mp.findroot(D,seed,tol=mp.mpf('1e-110'));off.append(dict(gamma=r['gamma'],coordinate_difference_from_90dps=fmt(abs(z-seed)),D_residual_120dps=mp.nstr(abs(D(z)),100)))
 mp.mp.dps=75;c=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1);independent=[]
 for re,im in [('0.73','85.8'),('0.81','331.1'),('1.1','595.1')]:
  z=mp.mpc(re,im);a=D(z);b=mp.dirichlet(z,[0,1,c,-c,-1]);F=lambda s:mp.exp(s*mp.log(5/mp.pi)/2+mp.loggamma((s+1)/2))*D(s)
  x,y=F(z),F(1-z);independent.append(dict(sigma=re,gamma=im,relative_mp_dirichlet_difference=fmt(abs(a-b)/max(abs(a),abs(b))),relative_functional_equation_difference=fmt(abs(x-y)/max(abs(x),abs(y)))))
 mp.mp.dps=75;minimum=None;h=mp.mpf('1e-22')
 for r in d['upper_half_plane_zeros']:
  z=mp.mpc(r['sigma'],r['gamma']);dv=abs((D(z+h)-D(z-h))/(2*h))
  if minimum is None or dv<minimum[0]:minimum=(dv,r)
  r['multiplicity']=1
 for r in d['critical_line_zeros']:r['multiplicity']=1
 for r in d['off_line_pairs']:r['listed_multiplicity']=1
 d['coefficient']=old['coefficient']
 d['source_script_sha256']={name:hashlib.sha256((P/name).read_bytes()).hexdigest() for name in ['extend.py','resume.py','fine_line_check.py','checks.py']}
 d['multiplicity_scope']='Listed simple roots; nonzero centered-difference derivatives checked numerically, not certified.'
 check=dict(status='DIAGNOSTIC_NEVER_A_PROOF',old_four_pairs_present=all(any(abs(mp.mpf(a['sigma_right'])-mp.mpf(b['sigma_right']))<mp.mpf('1e-70') and abs(mp.mpf(a['gamma'])-mp.mpf(b['gamma']))<mp.mpf('1e-70') for b in d['off_line_pairs']) for a in old['off_line_pairs']),fine_line_check_all_counts_match=all(r['bracket_count']==r['coarse_line_count'] for r in json.loads((P/'fine_line_check.json').read_text())),old_critical_prefix_coordinate_max_difference=fmt(max(errors)),off_line_90_vs_120dps=off,independent_mpmath_spot_checks=independent,smallest_numerical_Dprime=dict(value=fmt(minimum[0]),sigma=minimum[1]['sigma'],gamma=minimum[1]['gamma']),max_refined_residual=fmt(max(mp.mpf(r['residual']) for r in d['critical_line_zeros'])),all_30_bands_match=all(r['matched'] for r in d['contour_bands']),global_counts=[r['count'] for r in d['global_argument_count']],exterior_reason='For sigma>=2, |D(s)-1|<=zeta(2)-1<1 because |a(n)|<=1. Functional equation excludes completed zeros for sigma<=-1. Positive-height contour therefore includes all nontrivial upper-half-plane zeros if the numerical count is correct.',not_a_rigorous_contour_certificate=True)
 check['low_height_winding']=winding(-.001,.001,.025)
 d['low_height_winding']=check['low_height_winding']
 (P/'CHECKS.json').write_text(json.dumps(check,indent=2)+'\n');save(d)
 with (P/'off_line_pairs.csv').open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=list(d['off_line_pairs'][0]));w.writeheader();w.writerows(d['off_line_pairs'])
 print(json.dumps({k:v for k,v in check.items() if k not in ['off_line_90_vs_120dps']},indent=2))
if __name__=='__main__':main()
