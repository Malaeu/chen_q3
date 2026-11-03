"""Refine the found census at200dps; no additional root-search completeness claim."""
from extend import *

def main():
 start=time.monotonic();d=json.loads((P/'dh_zeros_600.json').read_text());mp.mp.dps=200;fmt200=lambda x:mp.nstr(x,200);delta=mp.mpf('1e-65');errors=[]
 for i,r in enumerate(d['critical_line_zeros']):
  seed=mp.mpf(r['gamma']);t=mp.findroot(Z,(seed,seed+delta),tol=mp.mpf('1e-190'),maxsteps=30);errors.append(abs(t-seed));r.update(gamma=fmt200(t),residual=fmt200(abs(D(mp.mpf('.5')+mp.j*t))))
  if i%100==0:print('LINE200',i,flush=True)
 for r in d['off_line_pairs']:
  seed=mp.mpc(r['sigma_right'],r['gamma']);z=mp.findroot(D,(seed,seed+delta),tol=mp.mpf('1e-190'),maxsteps=30);mirror=1-mp.conj(z);errors.append(abs(z-seed));r.update(sigma_right=fmt200(mp.re(z)),sigma_left=fmt200(mp.re(mirror)),gamma=fmt200(mp.im(z)),right_residual=fmt200(abs(D(z))),left_residual=fmt200(abs(D(mirror))))
 d['upper_half_plane_zeros']=[dict(sigma='0.5',gamma=r['gamma'],kind='critical_line',multiplicity=1) for r in d['critical_line_zeros']]
 for r in d['off_line_pairs']:
  for k in ['sigma_left','sigma_right']:d['upper_half_plane_zeros'].append(dict(sigma=r[k],gamma=r['gamma'],kind='off_line',multiplicity=1))
 d['upper_half_plane_zeros'].sort(key=lambda r:(mp.mpf(r['gamma']),mp.mpf(r['sigma'])));d['dps']=200;d['coefficient']=fmt200((mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1));d['refinement_200dps']=dict(seconds=time.monotonic()-start,max_coordinate_difference_from_saved_90dps=fmt200(max(errors)),max_D_residual=fmt200(max([mp.mpf(r['residual']) for r in d['critical_line_zeros']]+[mp.mpf(r[k]) for r in d['off_line_pairs'] for k in ['right_residual','left_residual']])),scope='Refinement of the same numerical census; discrete contour count diagnostics inherited unchanged.',script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest());(P/'dh_zeros_600_200dps.json').write_text(json.dumps(d,indent=2)+'\n');print('DONE',d['refinement_200dps'],flush=True)
if __name__=='__main__':main()
