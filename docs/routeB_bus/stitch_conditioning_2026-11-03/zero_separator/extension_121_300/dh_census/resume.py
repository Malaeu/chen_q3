"""Bounded Newton off-line search resuming saved contour/critical census."""
from extend import *

def bounded(seed,lo,hi):
 z=seed;h=mp.mpf('1e-8')
 for k in range(35):
  v=D(z)
  if abs(v)<mp.mpf('1e-25'):return z
  der=(D(z+h)-D(z-h))/(2*h)
  if abs(der)<mp.mpf('1e-18'):return None
  step=v/der
  if abs(step)>1:step/=abs(step)
  z-=step
  if not .2<float(mp.re(z))<1.99 or not lo-1<float(mp.im(z))<hi+1:return None
 return None

def main():
 start=time.monotonic();d=json.loads((P/'dh_zeros_600.json').read_text());old=json.loads(INPUT.read_text());pairs=[mp.mpc(r['sigma_right'],r['gamma']) for r in old['off_line_pairs']]
 resume_log=Path(os.environ['DH_RESUME_LOG']) if os.environ.get('DH_RESUME_LOG') else None
 for line in resume_log.read_text().splitlines() if resume_log and resume_log.exists() else []:
  if line.startswith('OFF_NEW'):
   _,x,y=line.split();pairs.append(mp.mpc(x,y))
 mp.mp.dps=40
 for rec in d['contour_bands']:
  target=rec['off_line_upper_count_needed']//2
  def local():return [z for z in pairs if rec['low']<float(mp.im(z))<rec['high']]
  if len(local())>=target:continue
  # Large gaps between critical roots are productive, then full quarter-height grid.
  gam=[rec['low']]+[float(r['gamma']) for r in d['critical_line_zeros'] if rec['low']<float(r['gamma'])<rec['high']]+[rec['high']]
  gaps=sorted(zip(gam,gam[1:]),key=lambda ab:ab[1]-ab[0],reverse=True)
  times=[(a+b)/2 for a,b in gaps]+[rec['low']+(j+.5)/4 for j in range(int((rec['high']-rec['low'])*4))]
  for t in times:
   for sig in ['.65','.85','1.15','1.65']:
    z=bounded(mp.mpc(sig,t),rec['low'],rec['high'])
    if z is None:continue
    if mp.re(z)<.5:z=1-mp.conj(z)
    if .500001<float(mp.re(z))<2 and rec['low']<float(mp.im(z))<rec['high'] and all(abs(z-p)>mp.mpf('1e-12') for p in pairs):
     pairs.append(z);print('OFF_NEW',fmt(mp.re(z)),fmt(mp.im(z)),flush=True)
     (P/'off_candidates.json').write_text(json.dumps([dict(sigma=fmt(mp.re(z)),gamma=fmt(mp.im(z))) for z in pairs],indent=2)+'\n')
   if len(local())>=target:break
  print('OFF_BAND',rec['low'],len(local()),'target',target,flush=True)
 mp.mp.dps=90;d['off_line_pairs']=[]
 for seed in sorted(pairs,key=lambda z:float(mp.im(z))):
  z=mp.findroot(D,seed,tol=mp.mpf('1e-82'),maxsteps=30);mirror=1-mp.conj(z)
  d['off_line_pairs'].append(dict(sigma_right=fmt(mp.re(z)),sigma_left=fmt(mp.re(mirror)),gamma=fmt(mp.im(z)),right_residual=fmt(abs(D(z))),left_residual=fmt(abs(D(mirror)))))
 d['upper_half_plane_zeros']=[dict(sigma='0.5',gamma=r['gamma'],kind='critical_line') for r in d['critical_line_zeros']]
 for r in d['off_line_pairs']:
  for k in ['sigma_left','sigma_right']:d['upper_half_plane_zeros'].append(dict(sigma=r[k],gamma=r['gamma'],kind='off_line'))
 d['upper_half_plane_zeros'].sort(key=lambda r:(mp.mpf(r['gamma']),mp.mpf(r['sigma'])));d['count_upper_half_plane']=len(d['upper_half_plane_zeros']);save(d);print('REFINED',len(d['off_line_pairs']),d['count_upper_half_plane'],flush=True)
 d['global_argument_count']=[]
 for h in [.25,.125,.0625]:
  rec=winding(.001,600,h);d['global_argument_count'].append(rec);save(d);print('GLOBAL',rec,flush=True)
 for rec in d['contour_bands']:
  rec['accounted_count']=sum(rec['low']<float(r['gamma'])<rec['high'] for r in d['upper_half_plane_zeros']);rec['matched']=rec['count']==rec['accounted_count']
 d['completeness_status']='NUMERICAL_COUNT_MATCH_NOT_INTERVAL_CERTIFIED' if all(r['matched'] for r in d['contour_bands']) and all(r['count']==d['count_upper_half_plane'] for r in d['global_argument_count']) else 'GAP';d['resume_seconds']=time.monotonic()-start;d['scan']=dict(step='.0625',critical_sign_brackets=len(d['critical_line_zeros']),no_interval_boundary_exclusion=True);save(d);print('DONE',d['completeness_status'],flush=True)
if __name__=='__main__':main()
