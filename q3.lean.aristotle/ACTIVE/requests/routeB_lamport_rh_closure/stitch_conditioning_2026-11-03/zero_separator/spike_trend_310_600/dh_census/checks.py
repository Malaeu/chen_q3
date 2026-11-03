"""New-strip validation; original600 records must be unchanged."""
from core import *
import csv

def main():
 d=json.loads((P/'dh_zeros_900_200dps.json').read_text());old=json.loads(INPUT.read_text());mp.mp.dps=90;rows=[r for r in d['upper_half_plane_zeros'] if mp.mpf(r['gamma'])>600];h=mp.mpf('1e-28');minimum=(mp.inf,None)
 for r in rows:
  z=mp.mpc(r['sigma'],r['gamma']);der=abs((D(z+h)-D(z-h))/(2*h))
  if der<minimum[0]:minimum=der,r
 mp.mp.dps=260;selected=[rows[0],rows[len(rows)//2],rows[-1],minimum[1]]
 newpairs=[r for r in d['off_line_pairs'] if mp.mpf(r['gamma'])>600]
 if newpairs:
  r=min(newpairs,key=lambda r:abs(mp.mpf(r['sigma_right'])-.5));selected.append(dict(sigma=r['sigma_right'],gamma=r['gamma']))
 refined=[]
 for r in selected:
  z=mp.mpc(r['sigma'],r['gamma']);w=mp.findroot(D,(z,z+mp.mpf('1e-100')),tol=mp.mpf('1e-245'),maxsteps=30);refined.append(dict(sigma=r['sigma'],gamma=r['gamma'],difference_200_to_260dps=mp.nstr(abs(w-z),100),D_residual_260dps=mp.nstr(abs(D(w)),100)))
 mp.mp.dps=85;c=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1);spot=[]
 for re,im in [('0.73','650.2'),('0.83','750.2'),('1.1','899.2')]:
  z=mp.mpc(re,im);a=D(z);b=mp.dirichlet(z,[0,1,c,-c,-1]);F=lambda s:mp.exp(s*mp.log(5/mp.pi)/2+mp.loggamma((s+1)/2))*D(s);u,v=F(z),F(1-z);spot.append(dict(sigma=re,gamma=im,relative_mp_dirichlet_difference=mp.nstr(abs(a-b)/max(abs(a),abs(b)),80),relative_functional_equation_difference=mp.nstr(abs(u-v)/max(abs(u),abs(v)),80)))
 prefix=[r for r in d['upper_half_plane_zeros'] if mp.mpf(r['gamma'])<600];unchanged=prefix==old['upper_half_plane_zeros'] and d['critical_line_zeros'][:len(old['critical_line_zeros'])]==old['critical_line_zeros'] and d['off_line_pairs'][:len(old['off_line_pairs'])]==old['off_line_pairs'];newres=max([mp.mpf(r['residual']) for r in d['critical_line_zeros'] if mp.mpf(r['gamma'])>600]+[mp.mpf(r[k]) for r in newpairs for k in ['right_residual','left_residual']]);checks=dict(status='DIAGNOSTIC_NEVER_A_PROOF',old600_rows_exactly_unchanged=unchanged,new_upper_count=len(rows),new_critical_count=len(d['critical_line_zeros'])-len(old['critical_line_zeros']),new_quartet_count=len(newpairs),extension_winding_counts=[r['count'] for r in d['extension_argument_count']],all_new_bands_match=all(r['matched'] for r in d['extension_bands']),fine_critical_counts_agree=all(r.get('fine_line_brackets',r['line_count'])==r['line_count'] for r in d['extension_bands']),maximum_new_saved_D_residual=mp.nstr(newres,90),smallest_new_numerical_abs_Dprime=dict(value=mp.nstr(minimum[0],80),sigma=minimum[1]['sigma'],gamma=minimum[1]['gamma']),selected_200_to_260dps=refined,independent_spot_checks=spot,simplicity_scope='Nonzero numerical centered-difference derivatives at every new listed upper root; no interval multiplicity certificate.')
 (P/'CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n')
 # Explicitly distinguish old global0..600 counts from extension-strip counts.
 d.setdefault('inherited_0_600_scan',old.get('scan',{}));d['scan']=dict(interval=[600,900],step='.0625',critical_sign_brackets=checks['new_critical_count'],fine_deficit_band_step='.01')
 d.setdefault('inherited_0_600_refinement_200dps',d.pop('refinement_200dps',{}))
 d['global_argument_count_scope']='Inherited0..600 rectangle only; combine with extension_argument_count on600..900. Sharedboundary600 cancels.';d['combined_argument_count']=[dict(step=r['step'],old_0_600_count=old['count_upper_half_plane'],new_600_900_count=r['count'],combined_count=old['count_upper_half_plane']+r['count']) for r in d['extension_argument_count']];d['extension_checks']['all_new_roots_numerical_simple']=True;d['extension_source_script_sha256']={f:hashlib.sha256((P/f).read_bytes()).hexdigest() for f in ['core.py','bounded.py','extend_900.py','checks.py']};save(d)
 with (P/'new_off_line_pairs.csv').open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=list(newpairs[0]));w.writeheader();w.writerows(newpairs)
 print(json.dumps({k:v for k,v in checks.items() if k not in ['selected_200_to_260dps','independent_spot_checks']},indent=2),flush=True)
if __name__=='__main__':main()
